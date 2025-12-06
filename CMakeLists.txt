cmake_minimum_required(VERSION 3.15)
project(TinyBackend LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

add_executable(run_tests tests/test_all.cpp)

add_executable(demo project1.cpp)
target_compile_definitions(demo PRIVATE BACKEND_MAIN)

enable_testing()
add_test(NAME backend_tests COMMAND run_tests)

