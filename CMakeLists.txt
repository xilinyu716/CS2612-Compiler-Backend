cmake_minimum_required(VERSION 3.15)

project(CompilerBackend)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Add executable for project1
add_executable(demo project1.cpp)

# Add executable for tests
# We need to include the current directory so project1.cpp can be included in test_all.cpp
include_directories(${CMAKE_CURRENT_SOURCE_DIR})
add_executable(test_all tests/test_all.cpp)

# Enable testing
enable_testing()
add_test(NAME TestAll COMMAND test_all)
