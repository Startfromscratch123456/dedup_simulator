cmake_minimum_required(VERSION 3.10)

set(CMAKE_RUNTIME_OUTPUT_DIRECTORY bin)

include_directories(../lib)

add_executable(main main.c)