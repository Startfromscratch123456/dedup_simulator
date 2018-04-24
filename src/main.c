#define _GNU_SOURCE
#define _LARGEFILE_SOURCE
#define _LARGEFILE64_SOURCE
#define _FILE_OFFSET_BITS 64

#include <sys/stat.h>
#include <unistd.h>
#include <time.h>
#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <inttypes.h>
#include <openssl/sha.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/types.h>
#include <unistd.h>
#include <getopt.h>
#include <sys/stat.h>
#include <signal.h>
#include <zlog.h>       // log
#include "dedup.h"
#include <stdbool.h>
#include <time.h>
#include "bplustree.h"


// ===================================================
//                  Global Variables
// ===================================================

struct g_args_t {
    char *hash_filename;
    int hash_fd;
    int run_mode;
    char *bplustree_filename;
    uint64_t cur_nbd_offset;
    zlog_category_t* write_block_category;
    zlog_category_t* log_error;
    struct bplus_tree *tree;
};
struct g_args_t g_args;

static void *zeros;
static struct hash_log_entry *cache;
static uint64_t hash_log_free_list;
static uint64_t data_log_free_offset;

enum mode{
    INIT_MODE = 0,
    RUN_MODE  = 1,
};

// ===================================================
//               Tool Functions: Seek
// ===================================================

#define SEEK_TO_BUCKET(fd, i) \
    do { \
        lseek64((fd), (i)*sizeof(hash_bucket), SEEK_SET); \
    } while(0)

#define SEEK_TO_HASH_LOG(fd, i) \
    do { \
        lseek64((fd), HASH_INDEX_SIZE + (i) * sizeof(struct hash_log_entry), SEEK_SET); \
    } while (0)


#define SEEK_TO_DATA_LOG(fd, offset) \
    do { \
        lseek64((fd), (offset), SEEK_SET); \
    } while(0)


static void fingerprint_to_str(char *dest, char *src)
{
    for (int i=0; i<SHA_DIGEST_LENGTH; i++)
        sprintf(&dest[i*2], "%02x", (unsigned int)src[i]);

}

// ===================================================
//                  Function Defines
// ===================================================


static void usage()
{
    fprintf(stderr, "Options:\n\n");
    fprintf(stderr, BOLD"    -h, --help\n" NONE "\tdisplay the help infomation\n\n");
    fprintf(stderr, BOLD"    -i, --init\n" NONE "\tspecify the nbd device and init\n\n");
    fprintf(stderr, BOLD"    -a, --hash-file\n" NONE "\tspecify the hash file\n\n");
    fprintf(stderr, BOLD"    -p, --physical-device\n" NONE "\tspecify the physical device or file\n\n");
    fprintf(stderr, BOLD"    -s, --space\n" NONE "\tspace mapping and specify space db file\n\n");
    fprintf(stderr, BOLD"    -b, --btree\n" NONE "\tb+tree mapping mode and specify b+tree db file\n\n");
}

static int fingerprint_is_zero(char *fingerprint)
{
    int i;
    for (i = 0; i < FINGERPRINT_SIZE; i++) {
        if (fingerprint[i])
            return 0;
    }
    return 1;
}


/**
 * Return the bucket which contains the given fingerprint
 */
static int hash_index_get_bucket(char *hash, hash_bucket *bucket)
{
    /* We don't need to look at the entire hash, just the last few bytes. */
    int32_t *hash_tail = (int32_t *)(hash + FINGERPRINT_SIZE - sizeof(int32_t));
    int bucket_index = *hash_tail % NBUCKETS;
    SEEK_TO_BUCKET(g_args.hash_fd, bucket_index);
    int err = read(g_args.hash_fd, bucket,
            sizeof(struct hash_index_entry) * ENTRIES_PER_BUCKET);
    assert(err == sizeof(struct hash_index_entry) * ENTRIES_PER_BUCKET);

    return 0;
}

static int hash_index_put_bucket(char *hash, hash_bucket *bucket)
{
    /* We don't need to look at the entire hash, just the last few bytes. */
    int32_t *hash_tail = (int32_t *)(hash + FINGERPRINT_SIZE - sizeof(int32_t));
    int bucket_index = *hash_tail % NBUCKETS;
    SEEK_TO_BUCKET(g_args.hash_fd, bucket_index);
    int err = write(g_args.hash_fd, bucket,
            sizeof(struct hash_index_entry) * ENTRIES_PER_BUCKET);
    assert(err == sizeof(struct hash_index_entry) * ENTRIES_PER_BUCKET);

    return 0;
}

static int hash_index_insert(char *hash, uint64_t hash_log_address)
{
    hash_bucket bucket;
    hash_index_get_bucket(hash, &bucket);

    for (int i = 0; i < ENTRIES_PER_BUCKET; i++)
        if (bucket[i].hash_log_address == 0) {
            /* We have found an empty slot. */
            memcpy(bucket[i].hash, hash, FINGERPRINT_SIZE);
            bucket[i].hash_log_address = hash_log_address;
            hash_index_put_bucket(hash, &bucket);
            return 0;
        }

    // Debug info. If we get to here, error occurs.
    char str_fp[SHA_DIGEST_LENGTH*2+1];
    fingerprint_to_str(str_fp, hash);
    printf("[HASH INDEX INSERT] | Debug | Hash: %s\n", str_fp);

    char log_line[1024*1024];
    sprintf(log_line, "[HASH INDEX INSERT] | Debug | Hash: %s", str_fp);
    zlog_info(g_args.log_error, log_line);

    /* We failed to find a slot. In the future it would be nice to have a more
     * sophisticated hash table that resolves collisions better. But for now we
     * just give up. */
    assert(0);
}

/**
 * Search the hash log address of given hash
 */
static uint64_t hash_index_lookup(char *hash)
{
    hash_bucket bucket;
    hash_index_get_bucket(hash, &bucket);

    for (int i = 0; i < ENTRIES_PER_BUCKET; i++)
        if (!memcmp(bucket[i].hash, hash, FINGERPRINT_SIZE))
            return bucket[i].hash_log_address;
    return -1;
}


/**
 * Given a fingerprint, remove the corresponding hash_index_entry in HASH INDEX TABLE
 */
static int hash_index_remove(char *hash)
{
    hash_bucket bucket;
    hash_index_get_bucket(hash, &bucket);

    for (int i = 0; i < ENTRIES_PER_BUCKET; i++)
        if (!memcmp(bucket[i].hash, hash, FINGERPRINT_SIZE)) {
            memset(bucket + i, 0, sizeof(struct hash_index_entry));
            hash_index_put_bucket(hash, &bucket);
            return 0;
        }

    return -1;
}

static uint64_t hash_log_new()
{
    uint64_t new_block = hash_log_free_list;
    SEEK_TO_HASH_LOG(g_args.hash_fd, new_block);
    int err = read(g_args.hash_fd, &hash_log_free_list, sizeof(uint64_t));
    assert(err == sizeof(uint64_t));
    return new_block;
}

/**
 * Free a hash_log_entry and change hash_log_free_list to it
 */
static int hash_log_free(uint64_t hash_log_address)
{
    SEEK_TO_HASH_LOG(g_args.hash_fd, hash_log_address);
    int err = write(g_args.hash_fd, &hash_log_free_list, sizeof(uint64_t));
    assert(err == sizeof(uint64_t));
    hash_log_free_list = hash_log_address;

    return 0;
}


static uint64_t physical_block_new(uint64_t block_size)
{
    return 0;
}

static int physical_block_free(uint64_t offest, uint64_t size)
{
    printf("Freed physical block:, offset: %lu, size: %lu\n", offest, size);

    return 0;
}


/**
 * Return the index where the given fingerprint SHOULD be found in
 * he cache
 */
static u_int32_t get_cache_index(char *fingerprint)
{
    /* It doesn't actually matter which bits we choose, as long as we are
     * consistent. So let's treat the first four bytes as an integer and take
     * the lower bits of that. */
    u_int32_t mask = (1 << CACHE_SIZE) - 1;
    u_int32_t result = ((u_int32_t *)fingerprint)[0] & mask;
    assert(result < mask);
    return result;
}

/**
 * Return a HAST LOG TABLE entry in terms of given fingerprint
 */
static struct hash_log_entry lookup_fingerprint(char *fingerprint)
{

    int err;

    // Search in CACHE
    u_int32_t index = get_cache_index(fingerprint);
    if (!memcmp(fingerprint, cache[index].fingerprint, FINGERPRINT_SIZE)) {
        // Awesome, this fingerprint is already cached, so we are good to go.
        return cache[index];
    }

    // Didn't hit in cache, so we have to look on disk.
    uint64_t hash_log_address = hash_index_lookup(fingerprint);
    assert(hash_log_address != (uint64_t)-1);



    // ==========================================
    //               update cache
    // ==========================================
    /* Now let's look up everything in the 4K block containing the hash log
     * entry we want. This way we can cache it all for later. */
    hash_log_address -= hash_log_address % HASH_LOG_BLOCK_SIZE;
    SEEK_TO_HASH_LOG(g_args.hash_fd, hash_log_address);
    struct hash_log_entry h;

    for (unsigned i = 0; i < HASH_LOG_BLOCK_SIZE/sizeof(struct hash_log_entry); i++) {
        err = read(g_args.hash_fd, &h, sizeof(struct hash_log_entry));
        assert(err == sizeof(struct hash_log_entry));

        u_int32_t j = get_cache_index(h.fingerprint);
        memcpy(cache + j, &h, FINGERPRINT_SIZE);
    }

    /* Now we should have looked up the fingerprint we wanted, along with a
     * bunch of others. */

    err = memcmp(fingerprint, cache[index].fingerprint, FINGERPRINT_SIZE);
    if (err != 0) {
        hash_log_address = hash_index_lookup(fingerprint);
        SEEK_TO_HASH_LOG(g_args.hash_fd, hash_log_address);
        struct hash_log_entry h_tmp;
        err = read(g_args.hash_fd, &h_tmp, sizeof(struct hash_log_entry));
//        fprintf(stderr, "hash log entry: %02x\nfingerprint: %02x\n", h_tmp.fingerprint, fingerprint);
    }

    return cache[index];
}

/**
 * Decrease the ref_count of a physical block
 */
static int decrement_refcount(char *fingerprint)
{
    // todo: decrement_refcount
    struct hash_log_entry hle;
    uint64_t hash_log_address = hash_index_lookup(fingerprint);
    SEEK_TO_HASH_LOG(g_args.hash_fd, hash_log_address);
    int err = read(g_args.hash_fd, &hle, sizeof(struct hash_log_entry));
    assert(err == sizeof(struct hash_log_entry));

    if (hle.ref_count > 1) {
        hle.ref_count--;
        SEEK_TO_HASH_LOG(g_args.hash_fd, hash_log_address);
        err = write(g_args.hash_fd, &hle, sizeof(struct hash_log_entry));
    } else {
        /* The ref_count is now zero, so we need to do some garbage collection
         * here. */
        hash_index_remove(fingerprint);
        physical_block_free(hle.data_log_offset, hle.block_size);
        hash_log_free(hash_log_address);
    }

    return 0;
}

static uint64_t get_nbd_offset(uint64_t chunk_size)
{
    uint64_t offset = g_args.cur_nbd_offset;
    g_args.cur_nbd_offset += chunk_size;
    return offset;
}


static int write_to_disk(int fd, uint64_t size)
{
    return 0;
}

static int write_one_chunk(uint64_t chunk_size, uint8_t *hash)
{
    ssize_t ret;
    struct block_map_entry bme;
    bme.nbd_offset = get_nbd_offset(chunk_size);
    bme.length = chunk_size;
    memcpy(bme.fingerprit, hash, FINGERPRINT_SIZE);

    bplus_tree_put(g_args.tree, bme.nbd_offset, bme);

    uint64_t hash_log_address;
    struct hash_log_entry hle;

    // See if this fingerprint is already stored in HASH_LOG
    hash_log_address = hash_index_lookup(hash);
    if (hash_log_address == (uint64_t)-1) {
        // This chunk is new
        memcpy(hle.fingerprint, hash, FINGERPRINT_SIZE);
        hle.data_log_offset = physical_block_new(chunk_size);
        hle.ref_count = 1;
        hle.block_size = chunk_size;

        hash_log_address = hash_log_new();

        // Update hash index
        hash_index_insert(hash, hash_log_address);
        // Update hash log
        SEEK_TO_HASH_LOG(g_args.hash_fd, hash_log_address);
        ret = write(g_args.hash_fd, &hle, sizeof(struct hash_log_entry));
        assert(ret == sizeof(struct hash_log_entry));
        write_to_disk(0, chunk_size);

    } else {
        // This chunk has already been stored.
        SEEK_TO_HASH_LOG(g_args.hash_fd, hash_log_address);
        ret = read(g_args.hash_fd, &hle, sizeof(struct hash_log_entry));
        assert(ret == sizeof(struct hash_log_entry));
        hle.ref_count ++;
        SEEK_TO_HASH_LOG(g_args.hash_fd, hash_log_address);
        ret = write(g_args.hash_fd, &hle, sizeof(struct hash_log_entry));
        assert(ret == sizeof(struct hash_log_entry));
    }

    return 0;

}


static int read_one_block(void *buf, uint32_t len, uint64_t offset)
{

    return 0;
}

static int dedup_read(void *buf, uint32_t len, uint64_t offset)
{


    char *bufi = buf;
    struct block_map_entry bmap_entry;
    struct hash_log_entry tmp_entry;

    bmap_entry = bplus_tree_get_fuzzy(g_args.tree, offset);

    /* If we don't BEGIN on a block boundary */
    if (offset != bmap_entry.start) {
        if(bmap_entry.length == 0) {
            memset(bufi, 0, len);
            return 0;
        }
        uint32_t read_size = bmap_entry.length - (offset - bmap_entry.start);
        assert(read_size >= 0);


        tmp_entry = lookup_fingerprint(bmap_entry.fingerprit);

        read_one_block(bufi, read_size, tmp_entry.data_log_offset);
        bufi += read_size;
        len -= read_size;
        offset += read_size;
    }

    while (len > 0 ) {
        bmap_entry = bplus_tree_get_fuzzy(g_args.tree, offset);
        if (len < bmap_entry.length)
            break;
        if (fingerprint_is_zero(bmap_entry.fingerprit)) {
            memset(bufi, 0, len);
            len = 0;
            continue;
        }
        assert(bmap_entry.length != 0);
        if (bmap_entry.length == 0) {
            printf("error!\n");
            memset(bufi, 0, len);
            return 0;
        }
        // We read a complete block

        tmp_entry = lookup_fingerprint(bmap_entry.fingerprit);
        read_one_block(bufi, bmap_entry.length, tmp_entry.data_log_offset);
        bufi += bmap_entry.length;
        len -= bmap_entry.length;
        offset += bmap_entry.length;
    }
    /* Now we get to the last block, it may be not a complete block*/
    if (len != 0) {
        read_one_block(bufi, len, offset);
    }

    return 0;
}

static void do_round_work()
{
    printf("Received SIGINT signal! Exiting...\n");
    ssize_t  ret;
    SEEK_TO_HASH_LOG(g_args.hash_fd, 0);
    ret = write(g_args.hash_fd, &hash_log_free_list, sizeof(uint64_t));
    assert(ret == sizeof(uint64_t));

    exit(0);
}


/**
 * Init in B+TREE mode.
 */
static int init()
{
    uint64_t i;
    int err;


    printf("init %llu buckets\n", NBUCKETS);

    /* We now initialize the hash log and data log. These start out empty, so we
     * put everything in the free list. It might be more efficient to stage this
     * in memory and then write it out in larger blocks. But the Linux buffer
     * cache will probably take care of that anyway for now. */
    for (i = 1; i <= NPHYS_BLOCKS; i++) {
        SEEK_TO_HASH_LOG(g_args.hash_fd, i - 1);
        err = write(g_args.hash_fd, &i, sizeof(uint64_t));
        assert(err == sizeof(uint64_t));
    }

    /* We use a list to manage free data log */



    return 0;
}




void static open_hash_file(char *filename)
{
    g_args.hash_fd = open64(filename, O_CREAT|O_RDWR|O_LARGEFILE);
    assert(g_args.hash_fd != -1);
}

/**
 * Parse cmd args
 */
void parse_command_line(int argc, char *argv[])
{
    /* command line args */
    const char *opt_string = "i:n:h:b:a";
    const struct option long_opts[] = {
            {"init", required_argument, NULL, 'i'},
            {"nbd", required_argument, NULL, 'n'},
            {"hash-file", required_argument, NULL, 'a'},
            {"help", no_argument, NULL, 'h'},
            {"bplustree", required_argument, NULL, 'b'},
            {NULL, 0, NULL, NULL},
    };

    // default opts
    g_args.hash_filename = "./hash.db";
    g_args.bplustree_filename = "./bptree.db";

    int opt = getopt_long(argc, argv, opt_string, long_opts, NULL);
    while( opt != -1 ) {
        switch(opt) {
            case 'a':   // hash data file
                g_args.hash_filename = optarg;
                break;
            case 'i':   // init mode
                g_args.run_mode = INIT_MODE;
                break;
            case 'n':   // nbd device
                g_args.run_mode = RUN_MODE;
                break;
            case 'b':   // b+tree mode
                g_args.bplustree_filename = optarg;
                break;
            case 'h':   // help
            default:
                usage();
                break;
        }
        opt = getopt_long(argc, argv, opt_string, long_opts, NULL);
    }
}

/**
 * Main entry
 */
int main(int argc, char *argv[])
{
    ssize_t err;

    /* First, we parse the cmd line */
    parse_command_line(argc, argv);

    g_args.tree = bplus_tree_init(g_args.bplustree_filename, 16777216*16);
    open_hash_file(g_args.hash_filename);



    /* Init zeros */
    zeros = mmap(NULL, HASH_INDEX_SIZE, PROT_READ, MAP_PRIVATE | MAP_ANONYMOUS, g_args.hash_fd, 0);
    assert(zeros != (void *) -1);


    ////////////////////////////////////////////////
    ////////////         INIT MODE        //////////
    ////////////////////////////////////////////////
    if ( g_args.run_mode == INIT_MODE ) {
        fprintf(stdout, "Performing Initialization!\n");
        init();
        bplus_tree_deinit(g_args.tree);
        return 0;
    ////////////////////////////////////////////////
    ////////////        NORMAL MODE       //////////
    ////////////////////////////////////////////////
    } else if ( g_args.run_mode == RUN_MODE ){
        /* By convention the first entry in the hash log is a pointer to the hash
         * log free list. Likewise for the data log. */
        SEEK_TO_HASH_LOG(g_args.hash_fd, 0);
        err = read(g_args.hash_fd, &hash_log_free_list, sizeof(uint64_t));
        assert( err == sizeof(uint64_t));

        data_log_free_offset = 0;

        /* Listen SIGINT signal */
        signal(SIGINT, &do_round_work);



        cache = calloc(1 << CACHE_SIZE, sizeof(struct hash_log_entry));

        /* Init zlog */
        err = zlog_init("../../config/zlog.conf");
        if(err) {
            fprintf(stderr, "zlog init failed\n");
            return -1;
        }
        g_args.write_block_category = zlog_get_category("write_block");
        if (!g_args.write_block_category) {
            fprintf(stderr, "get write_block_category failed\n");
            zlog_fini();
            return -2;
        }
        g_args.log_error = zlog_get_category("error");
        if (!g_args.log_error) {
            fprintf(stderr, "get log_error failed\n");
            zlog_fini();
            return -2;
        }
        last_request.length = 0;


        zlog_fini();
        bplus_tree_deinit(g_args.tree);
        return 0;
    }
}
