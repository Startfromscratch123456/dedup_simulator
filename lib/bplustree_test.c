#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <zconf.h>

#include "dedup.h"
#include "bplustree.h"



int main(void)
{
    struct bplus_tree* tree;
    struct block_map_entry ble;
    if (access("./bptree.db", F_OK) != -1) {
        if (remove("./bptree.db") == 0) {
            printf("Removed existed file ./bptree.db\n");
        } else {
            perror("Remove B+Tree db file");
        }
    }
    if (access("./bptree.db.boot", F_OK) != -1) {
        if (remove("./bptree.db.boot") == 0) {
            printf("Removed existed file ./bptree.db.boot\n");
        } else {
            perror("Remove B+Tree boot file");
        }
    }

    tree = bplus_tree_init("./bptree.db", 4096);
    sprintf(ble.fingerprit, "ab:cd:ef:gh");
    for (uint64_t i = 0; i< 100; i++) {
        ble.length = i;
        ble.nbd_offset = i;
        bplus_tree_put(tree, i, ble);
    }

    bplus_tree_dump(tree);
    bplus_tree_deinit(tree);

    return 0;
}
