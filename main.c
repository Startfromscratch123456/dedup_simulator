#define _GNU_SOURCE
#define _LARGEFILE_SOURCE
#define _LARGEFILE64_SOURCE
#define _FILE_OFFSET_BITS 64

#include <sys/stat.h>
#include <stdint.h>
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
#include <signal.h>
#include <zlog.h>       // log
#include "dedup.h"
#include <stdbool.h>
#include <time.h>
#include <malloc.h>
#include "bplustree.h"
#include "libhashfile.h"


#define PRINTLN printf("\n")
#define LOG_LINE 4096

// ===================================================
//                  Global Variables
// ===================================================

struct g_args_t {
    uint64_t n_hash_index;
    uint64_t n_hash_log;
    uint64_t n_bpt_node;
    int image_fd;
    int RW;
    int MAP;
    uint32_t fingerprint_size;  // in bytes
    char *hash_filename;
    int hash_fd;
    int run_mode;
    char *bplustree_filename;
    char *dataset_filename;
    uint64_t cur_nbd_offset;
    zlog_category_t* write_block_category;
    zlog_category_t* log_error;
    struct bplus_tree *tree;
    bool log_on;
};
struct g_args_t g_args;

static void *zeros;
static struct hash_log_entry *cache;
static uint64_t hash_log_free_list;
static uint64_t data_log_free_offset;

enum mode{
    INIT_MODE = 0,
    RUN_MODE  = 1,
    WRITE_MODE = 2,
    READ_MODE = 3,
    BPTREE_MODE = 4,
    SPACE_MODE = 5,

};

clock_t timer_write_space = 0;
clock_t timer_write_tree = 0;
clock_t timer_read_space = 0;
clock_t timer_read_tree = 0;

// ===================================================
//               Tool Functions: Seek
// ===================================================

#define SEEK_TO_BUCKET(fd, i) \
    do { \
        if (g_args.MAP == BPTREE_MODE ) \
            lseek64((fd), (i)*sizeof(hash_bucket), SEEK_SET); \
        else if (g_args.MAP == SPACE_MODE) \
            lseek64((fd), SPACE_SIZE + (i)*sizeof(hash_bucket), SEEK_SET); \
    } while(0)

#define SEEK_TO_HASH_LOG(fd, i) \
    do { \
        if (g_args.MAP == BPTREE_MODE ) \
            lseek64((fd), HASH_INDEX_SIZE + (i) * sizeof(struct hash_log_entry), SEEK_SET); \
        else if (g_args.MAP == SPACE_MODE) \
            lseek64((fd), SPACE_SIZE + HASH_INDEX_SIZE + (i) * sizeof(struct hash_log_entry), SEEK_SET); \
    } while (0)

//#define SEEK_TO_SPACE(fd, i) \
//    do { \
//        lseek64((fd), (i) * SPACE_LENGTH, SEEK_SET); \
//    } while (0)

static void SEEK_TO_SPACE(const int fd, const uint64_t i)
{
    off_t err = lseek64(fd, i * SPACE_LENGTH, SEEK_SET);
    assert(err != -1);
}

// ===================================================
//                  Function Defines
// ===================================================


static void usage()
{
    fprintf(stderr, "Options:\n\n");

    fprintf(stderr, "    -d, --dataset\n" "\tdata set file\n");
    fprintf(stderr, "    -i, --init\n"  "\tspecify the nbd device and init\n\n");
    fprintf(stderr, "    -a, --hash-file\n"  "\tspecify the hash file\n\n");
    fprintf(stderr, "    -p, --physical-device\n"  "\tspecify the physical device or file\n\n");

    fprintf(stderr, "\n");
    fprintf(stderr, "    -b, --btree\n"  "\tb+tree mapping mode and specify b+tree db file\n\n");
    fprintf(stderr, "    -s, --space\n" "\t space mode\n");

    fprintf(stderr, "\n");
    printf(stderr, "     -w, --write\n"  "\twrite mode\n");
    printf(stderr, "     -r, --read\n"  "\tread mode\n");

    fprintf(stderr, "\n");
    fprintf(stderr, "    -h, --help\n"  "\tdisplay the help infomation\n\n");
    exit(0);
}

static int fingerprint_is_zero(char *fingerprint)
{
    int i;
    for (i = 0; i < g_args.fingerprint_size; i++) {
        if (fingerprint[i])
            return 0;
    }
    return 1;
}

static void print_chunk_hash(const uint8_t *hash,
                             int hash_size_in_bytes)
{
    int j;

    printf("%.2hhx", hash[0]);
    for (j = 1; j < hash_size_in_bytes; j++)
        printf(":%.2hhx", hash[j]);
}

/**
 * Return the bucket which contains the given fingerprint
 */
static int hash_index_get_bucket(char *hash, hash_bucket *bucket)
{
    /* We don't need to look at the entire hash, just the last few bytes. */
    int32_t *hash_tail = (int32_t *)(hash + g_args.fingerprint_size - sizeof(int32_t));
    uint64_t bucket_index = *hash_tail % NBUCKETS;
    SEEK_TO_BUCKET(g_args.hash_fd, bucket_index);
    ssize_t err = read(g_args.hash_fd, bucket, sizeof(struct hash_index_entry) * ENTRIES_PER_BUCKET);
    assert(err == sizeof(struct hash_index_entry) * ENTRIES_PER_BUCKET);

    return 0;
}

static int hash_index_put_bucket(char *hash, hash_bucket *bucket)
{
    /* We don't need to look at the entire hash, just the last few bytes. */
    int32_t *hash_tail = (int32_t *)(hash + g_args.fingerprint_size - sizeof(int32_t));
    uint64_t bucket_index = *hash_tail % NBUCKETS;
    SEEK_TO_BUCKET(g_args.hash_fd, bucket_index);
    ssize_t err = write(g_args.hash_fd, bucket, sizeof(struct hash_index_entry) * ENTRIES_PER_BUCKET);
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
            memcpy(bucket[i].hash, hash, g_args.fingerprint_size);
            bucket[i].hash_log_address = hash_log_address;
            hash_index_put_bucket(hash, &bucket);
            return 0;
        }

    /* We failed to find a slot. In the future it would be nice to have a more
     * sophisticated hash table that resolves collisions better. But for now we
     * just give up. */
    assert(0);
}


static int hash_get_space(uint64_t offset, hash_space *space)
{
    uint64_t space_n = offset / SPACE_LENGTH;
    SEEK_TO_SPACE(g_args.hash_fd, space_n);
    ssize_t err = read(g_args.hash_fd, space, sizeof(struct block_map_entry) * ENTRIES_PER_SPACE);
    assert(err == sizeof(struct block_map_entry) * ENTRIES_PER_SPACE);

    return 0;
}


static int hash_put_space(uint64_t offset, hash_space *space)
{
    uint64_t space_n = offset / SPACE_LENGTH;
    SEEK_TO_SPACE(g_args.hash_fd, space_n);
    ssize_t err = write(g_args.hash_fd, space, sizeof(struct block_map_entry) * ENTRIES_PER_SPACE);
    assert(err == sizeof(struct block_map_entry) * ENTRIES_PER_SPACE);

    return 0;
}

static int hash_space_insert(uint64_t offset, struct block_map_entry ble)
{
    hash_space space;

    hash_get_space(offset, &space);

    for (int i = 0; i < ENTRIES_PER_SPACE; i ++) {
        if (space[i].length == 0) {
            /// We have found an empty slot.
            memcpy(space + i, &block_map_entry, sizeof(struct block_map_entry));
            hash_put_space(offset, &space);
            return 0;
        }
    }

    /// Failed to find a slot.
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
        if (!memcmp(bucket[i].hash, hash, g_args.fingerprint_size))
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
        if (!memcmp(bucket[i].hash, hash, g_args.fingerprint_size)) {
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
    ssize_t err = read(g_args.hash_fd, &hash_log_free_list, sizeof(uint64_t));
    assert(err == sizeof(uint64_t));
    return new_block;
}

/**
 * Free a hash_log_entry and change hash_log_free_list to it
 */
static int hash_log_free(uint64_t hash_log_address)
{
    SEEK_TO_HASH_LOG(g_args.hash_fd, hash_log_address);
    ssize_t err = write(g_args.hash_fd, &hash_log_free_list, sizeof(uint64_t));
    assert(err == sizeof(uint64_t));
    hash_log_free_list = hash_log_address;

    return 0;
}


static uint64_t physical_block_new(uint64_t block_size)
{
    uint64_t offset = data_log_free_offset;
    data_log_free_offset += block_size;

    return offset;
}

static int physical_block_free(uint64_t offest, uint64_t size)
{
    printf("Freed physical block, offset: %lu, size: %lu\n", offest, size);

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
    if (result > 20) {
        int i = 0;
    }
    assert(result < mask);

    return result;
}

/**
 * Return a HAST LOG TABLE entry in terms of given fingerprint
 */
static struct hash_log_entry lookup_fingerprint(char *fingerprint)
{

    ssize_t err;

    // Search in CACHE
    u_int32_t index = get_cache_index(fingerprint);
    if (!memcmp(fingerprint, cache[index].fingerprint, g_args.fingerprint_size)) {
        // Awesome, this fingerprint is already cached, so we are good to go.
        return cache[index];
    }

    // Didn't hit in cache, so we have to look on disk.
    uint64_t hash_log_address = hash_index_lookup(fingerprint);
    assert(hash_log_address != (uint64_t)-1);

    struct hash_log_entry hle;
    SEEK_TO_HASH_LOG(g_args.hash_fd, hash_log_address);
    err = read(g_args.hash_fd, &hle, sizeof(struct hash_log_entry));
    assert(err == sizeof(struct hash_log_entry));
    return hle;



    // ==========================================
    //               update cache
    // ==========================================
    /* Now let's look up everything in the 4K block containing the hash log
     * entry we want. This way we can cache it all for later. */
    hash_log_address = hash_log_address % HASH_LOG_BLOCK_SIZE;
    SEEK_TO_HASH_LOG(g_args.hash_fd, hash_log_address);
    struct hash_log_entry h;

    for (unsigned i = 0; i < HASH_LOG_BLOCK_SIZE/sizeof(struct hash_log_entry); i++) {
        err = read(g_args.hash_fd, &h, sizeof(struct hash_log_entry));
        assert(err == sizeof(struct hash_log_entry));

        u_int32_t j = get_cache_index(h.fingerprint);

        if (i == 0 && j != index) {
            int a = 0;
        }

        printf("[UPDATE CACHE : %u] | phy off: %lu, block size: %lu\n", index, h.data_log_offset, h.block_size);

        memcpy(cache + j, &h, sizeof(struct hash_log_entry));
    }

    /* Now we should have looked up the fingerprint we wanted, along with a
     * bunch of others. */

    err = memcmp(fingerprint, cache[index].fingerprint, g_args.fingerprint_size);
    assert( err == 0 );


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
    ssize_t err = read(g_args.hash_fd, &hle, sizeof(struct hash_log_entry));
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

static int read_one_chunk(uint8_t *hash) {
    /// Since the data set provides fingerprint directly, we don't need search from B+tree or Space
    char log_string[LOG_LINE];
    struct hash_log_entry hle = lookup_fingerprint((char*)hash);
    sprintf(log_string, "[READ] | phy addr: %lu, chunk size: %lu, hash: ", hle.data_log_offset, hle.block_size);


    printf(log_string);
    print_chunk_hash(hash, g_args.fingerprint_size);
    PRINTLN;

    return 0;
}

static int read_one_chunk_by_off(uint64_t offset, void* buf)
{
    printf("[READ] | nbd offset: %lu\n", offset);
    struct block_map_entry ble;
    char log_line[MAXLINE];

    if (g_args.MAP == BPTREE_MODE) {
        clock_t read_tree_start = clock();
        ble = bplus_tree_get_fuzzy(g_args.tree, offset);
//        assert(ble.length != 0);
        printf("[TREE] | off: %lu, len: %lu fingerprint: ", ble.nbd_offset, ble.length);
        print_chunk_hash((uint8_t *)ble.fingerprit, g_args.fingerprint_size);
        PRINTLN;
        timer_read_tree += clock() - read_tree_start;
    } else {
        clock_t read_space_start = clock();
        hash_space space;
        hash_get_space(offset, &space);
        for (int i = 0; i < ENTRIES_PER_SPACE; i ++) {
            if (space[i].nbd_offset < offset && space[i].nbd_offset + space[i].length > offset) {
                ble = space[i];
            }
        }
        timer_read_space += clock() - read_space_start;
    }
    read_one_chunk((uint8_t *)ble.fingerprit);
}

static int write_to_disk(int fd, uint64_t size)
{
    return 0;
}

static int write_one_chunk(uint64_t offset, uint64_t chunk_size, uint8_t *hash)
{
    clock_t w_space_start;
    clock_t w_space_end;
    clock_t w_tree_start;
    clock_t w_tree_end;
    ssize_t ret;
    char log_line[MAXLINE];
    struct block_map_entry bme;

    bme.nbd_offset = offset;
    bme.length = chunk_size;
    memcpy(bme.fingerprit, hash, g_args.fingerprint_size);
    g_args.n_bpt_node ++;

    if (g_args.MAP == BPTREE_MODE) {
        w_tree_start = clock();
        bplus_tree_put(g_args.tree, offset, bme);
        w_tree_end = clock();
        timer_write_tree += w_tree_end - w_tree_start;
    }
    else if (g_args.MAP == SPACE_MODE) {
        w_space_start = clock();
        hash_space_insert(offset, bme);
        w_space_end = clock();
        timer_write_space += w_space_end - w_space_start;
    }


    uint64_t hash_log_address;
    struct hash_log_entry hle;

    // See if this fingerprint is already stored in HASH_LOG
    hash_log_address = hash_index_lookup((char*)hash);
    if (hash_log_address == (uint64_t)-1) {
        // This chunk is new

        g_args.n_hash_log ++;
        g_args.n_hash_index ++;

        memcpy(hle.fingerprint, hash, g_args.fingerprint_size);
        hle.data_log_offset = physical_block_new(chunk_size);
        hle.ref_count = 1;
        hle.block_size = chunk_size;

        sprintf(log_line, "[NEW] | nbd_off: %lu, len: %lu, offset: %lu",bme.nbd_offset, chunk_size, hle.data_log_offset);
        printf(log_line);
        PRINTLN;
        if (g_args.log_on) {
            zlog_info(g_args.write_block_category, log_line);
        }


        hash_log_address = hash_log_new();

        // Update hash index
        hash_index_insert((char*)hash, hash_log_address);
        // Update hash log
        SEEK_TO_HASH_LOG(g_args.hash_fd, hash_log_address);
        ret = write(g_args.hash_fd, &hle, sizeof(struct hash_log_entry));
        assert(ret == sizeof(struct hash_log_entry));
        // We don't really write data to disk.
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

        sprintf(log_line, "[REDUNDANT] | nbd_off: %lu, len: %lu, offset: %lu",
                bme.nbd_offset, chunk_size, hle.data_log_offset);
        printf(log_line);
        PRINTLN;
        if (g_args.log_on) {
            zlog_info(g_args.write_block_category, log_line);
        }

    }

    return 0;

}



static void receive_sigint(int sig)
{
    printf("Received SIGINT signal! Exiting...\n");
    ssize_t  ret;
    SEEK_TO_HASH_LOG(g_args.hash_fd, 0);
    ret = write(g_args.hash_fd, &hash_log_free_list, sizeof(uint64_t));
    assert(ret == sizeof(uint64_t));

    if (g_args.log_on) {
        zlog_fini();
    }
    if (g_args.MAP == BPTREE_MODE) {
        bplus_tree_deinit(g_args.tree);
    }
    exit(0);
}



static int read_datafile(char *datafile_name)
{
    struct hashfile_handle *handle;
    const struct chunk_info *ci;
    int ret;
    uint64_t n_chunks;

    handle = hashfile_open(datafile_name);
    if (!handle) {
        fprintf(stderr, "Error opening dataset: %d!", errno);
        return -1;
    }

    /* Print some information about the hash file */
    g_args.fingerprint_size = hashfile_hash_size(handle) / 8;

    /* Go over the files in a hashfile */
    n_chunks = 0;
    while (1) {
        ret = hashfile_next_file(handle);
        if (ret < 0) {
            fprintf(stderr,
                    "Cannot get next file from dataset: %d!\n",
                    errno);
            return -1;
        }

        /* exit the loop if it was the last file */
        if (ret == 0)
            break;

        printf("\nFile path: %s\n", hashfile_curfile_path(handle));
        printf("File size: %"PRIu64 " B\n",
               hashfile_curfile_size(handle));
        printf("Chunks number: %" PRIu64 "\n",
               hashfile_curfile_numchunks(handle));

        /* Go over the chunks in the current file */
        while (1) {
            ci = hashfile_next_chunk(handle);
            if (!ci) /* exit the loop if it was the last chunk */
                break;
            n_chunks ++;
            if (g_args.RW == WRITE_MODE) {
                write_one_chunk(get_nbd_offset(ci->size), ci->size, ci->hash);
            } else if (g_args.RW == READ_MODE) {
                read_one_chunk_by_off(get_nbd_offset(ci->size), NULL);
            }
            if (n_chunks >= 50)
                return 0;
        }
    }

    hashfile_close(handle);

    return 0;
}

void static open_hash_file(char *filename)
{
    g_args.hash_fd = open64(filename, O_CREAT|O_RDWR|O_LARGEFILE, 0755);
    assert(g_args.hash_fd != -1);
}

static int init()
{
    uint64_t i;
    ssize_t err;

    /// delete old db file
    if (access(g_args.bplustree_filename, F_OK) != -1) {
        if (remove(g_args.bplustree_filename) == 0) {
            printf("Removed existed file %s\n", g_args.bplustree_filename);
        } else {
            perror("Remove B+Tree db file");
        }
    }
    char tree_boot_filename[255];
    sprintf(tree_boot_filename, "%s.boot", g_args.bplustree_filename);
    if (access(tree_boot_filename, F_OK) != -1) {
        if (remove(tree_boot_filename) == 0) {
            printf("Removed existed file %s\n", tree_boot_filename);
        } else {
            perror("Remove B+Tree boot file");
        }
    }
    if (access(g_args.hash_filename, F_OK) != -1) {
        if (remove(g_args.hash_filename) == 0) {
            printf("Removed existed file %s\n", g_args.hash_filename);
        } else {
            perror("Remove B+Tree db file");
        }
    }
    printf("Preparing for new db file!\n");
    open_hash_file(g_args.hash_filename);

    /// no matter in space mode or b+tree mode, we only need to init HASH_LOG area.
    /// HASH_INDEX and SPACE area will be a blank hole
    for (i = 1; i <= N_BLOCKS; i++) {
        SEEK_TO_HASH_LOG(g_args.hash_fd, i - 1);
        err = write(g_args.hash_fd, &i, sizeof(uint64_t));
        assert(err == sizeof(uint64_t));
    }


    return 0;
}



void set_default_options()
{
    g_args.log_on = false;  // don't log for now
    g_args.hash_filename = "./hash.db";
    g_args.bplustree_filename = "./bptree.db";
    g_args.dataset_filename = "/home/cyril/dataset/kernel/fslhomes-kernel";
    g_args.RW = READ_MODE;
    g_args.MAP = BPTREE_MODE;
    g_args.run_mode = RUN_MODE;
}

void parse_command_line(int argc, char *argv[])
{
    /* command line args */
    const char *opt_string = "i:a:h:b:d:w:r";
    const struct option long_opts[] = {
            {"init", no_argument, NULL, 'i'},
            {"hash-file", required_argument, NULL, 'a'},
            {"help", no_argument, NULL, 'h'},
            {"bplustree", required_argument, NULL, 'b'},
            {"space", no_argument, NULL, 's'},
            {"dataset", required_argument, NULL, 'd'},
            {"write", no_argument, NULL, 'w'},
            {"read", no_argument, NULL, 'r'},
            {NULL, 0, NULL, NULL},
    };

    set_default_options();

    int opt = getopt_long(argc, argv, opt_string, long_opts, NULL);
    while( opt != -1 ) {
        switch(opt) {
            case 'w':
                g_args.run_mode = RUN_MODE;
                g_args.RW = WRITE_MODE;
                break;
            case 'r':
                g_args.run_mode = RUN_MODE;
                g_args.RW = READ_MODE;
                break;
            case 'a':   // hash data file
                g_args.hash_filename = optarg;
                break;
            case 'i':   // init mode
                g_args.run_mode = INIT_MODE;
                break;

            case 'b':   // b+tree mode
                g_args.bplustree_filename = optarg;
                break;
            case 's':
                g_args.MAP = SPACE_MODE;
                break;

            case 'd':   // dataset file
                g_args.dataset_filename = optarg;
                break;
            case 'h':   // help
            default:
                usage();
                break;
        }
        opt = getopt_long(argc, argv, opt_string, long_opts, NULL);
    }
}

void print_statistic_info()
{
    // write mode
    if (g_args.RW == WRITE_MODE) {
        printf("\n\n===================== SIZE ======================\n");
        printf("B+Tree(/Space) size: %.3f M.\n", g_args.n_bpt_node * sizeof(struct block_map_entry)/1024.0f/1024.0f);
        printf("Hash Index size: %.3f M.\n", g_args.n_hash_index* sizeof(struct hash_index_entry)/1024.0f/1024.0f);
        printf("Hash Log size: %.3f M.\n", g_args.n_hash_log* sizeof(struct hash_log_entry)/1024.0f/1024.0f);
        printf("\n===================== TIME-W ======================\n");
        if (g_args.MAP == SPACE_MODE) {
            printf("Write Space: %.3f s.\n", (float)timer_write_space/CLOCKS_PER_SEC);

        } else {
            printf("Write Tree: %.3f s.\n", (float)timer_write_tree/CLOCKS_PER_SEC);
        }
    }
    // read mode
    else {
        printf("\n===================== TIME-R ======================\n");
        if (g_args.MAP == BPTREE_MODE)
            printf("Read Tree: %.3f s.\n", (float)timer_read_tree/CLOCKS_PER_SEC);
        else
            printf("Read Space: %.3f s.\n", (float)timer_read_space/CLOCKS_PER_SEC);
    }
}

int main(int argc, char *argv[])
{
    /* First, we parse the cmd line */
    parse_command_line(argc, argv);

    // Init
    if (g_args.run_mode == INIT_MODE) {
        fprintf(stdout, "Performing Initialization!\n");
        init();
        if (g_args.MAP == BPTREE_MODE)
            g_args.tree = bplus_tree_init(g_args.bplustree_filename, 4096);
        if (g_args.MAP == BPTREE_MODE) {
            bplus_tree_deinit(g_args.tree);
        }
        close(g_args.hash_fd);
        return 0;
    }

    ssize_t err;
    g_args.cur_nbd_offset = 0;

    if (g_args.MAP == BPTREE_MODE)
        g_args.tree = bplus_tree_init(g_args.bplustree_filename, 4096);
    open_hash_file(g_args.hash_filename);       // open hash table's db file

    g_args.n_bpt_node = 0;
    g_args.n_hash_index = 0;
    g_args.n_hash_log = 0;
    /* By convention the first entry in the hash log is a pointer to the hash
     * log free list. Likewise for the data log. */
    SEEK_TO_HASH_LOG(g_args.hash_fd, 0);
    err = read(g_args.hash_fd, &hash_log_free_list, sizeof(uint64_t));
    assert(err == sizeof(uint64_t));
//        hash_log_free_list = 1;


    /* Listen SIGINT signal */
    signal(SIGINT, &receive_sigint);

    /// 1 << CACHE_SIZE = 2^CACHE_SIZE
    cache = calloc(1 << CACHE_SIZE, sizeof(struct hash_log_entry));

    if (g_args.log_on) {
        /* Init zlog */
        err = zlog_init("../config/zlog.conf");
        if(err) {
            fprintf(stderr, "zlog init failed\n");
            return -1;
        }
        g_args.write_block_category = zlog_get_category("ds");
        if (!g_args.write_block_category) {
            fprintf(stderr, "get ds_log_category failed\n");
            zlog_fini();
            return -2;
        }
        g_args.log_error = zlog_get_category("ds_error");
        if (!g_args.log_error) {
            fprintf(stderr, "get log_error_category failed\n");
            zlog_fini();
            return -2;
        }
    }


    read_datafile(g_args.dataset_filename);

    print_statistic_info();

    SEEK_TO_HASH_LOG(g_args.hash_fd, 0);
    err = write(g_args.hash_fd, &hash_log_free_list, sizeof(uint64_t));
    assert(err == sizeof(uint64_t));

    if (g_args.log_on) {
        zlog_fini();
    }

    if (g_args.MAP == BPTREE_MODE) {
        bplus_tree_deinit(g_args.tree);
    }
    close(g_args.hash_fd);
    return 0;

}
