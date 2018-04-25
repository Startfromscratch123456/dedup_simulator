set(LIBRARY_OUTPUT_PATH ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/lib)
add_library(hashfile STATIC libhashfile.c)
add_library(bplustree STATIC bplustree.c)