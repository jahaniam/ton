cmake_minimum_required(VERSION 3.5 FATAL_ERROR)

add_library(contest-solution STATIC 
    solution.hpp 
    solution.cpp 
    contest-validate-query.hpp 
    contest-validate-query.cpp
    contest-validate-query_p1.cpp
    contest-validate-query_p2.cpp
    contest-validate-query_p3.cpp
    contest-validate-query_p4.cpp
    contest-validate-query_p5.cpp
    contest-validate-query_p6.cpp
    contest-validate-query_p7.cpp
    contest-validate-query_p8.cpp
    contest-validate-query_p9.cpp
    contest-validate-query_p10.cpp
    contest-validate-query_p11.cpp
)
target_include_directories(contest-solution PUBLIC $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/../..>)
target_include_directories(contest-solution PUBLIC $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/../../validator>)
target_link_libraries(contest-solution PRIVATE tdactor tdutils ton_block ton_validator validator ton_crypto)