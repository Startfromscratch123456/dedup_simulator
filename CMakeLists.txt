cmake_minimum_required(VERSION 3.5.1)

set(${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/bin)

ADD_SUBDIRECTORY(lib)
INCLUDE_DIRECTORIES(lib)

add_executable(main main.c)
target_link_libraries(main zlog bplustree hashfile)