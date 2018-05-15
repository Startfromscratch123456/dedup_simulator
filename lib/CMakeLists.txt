set(LIBRARY_OUTPUT_PATH ${BUILD_DIR}/lib)
add_library(hashfile STATIC libhashfile.c)
add_library(bplustree STATIC bplustree.c)

add_executable(tree_test bplustree_test.c)
target_link_libraries(tree_test bplustree)