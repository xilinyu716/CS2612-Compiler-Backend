#!/usr/bin/env bash
set -euo pipefail

if command -v cmake >/dev/null 2>&1; then
  cmake -S . -B build -DCMAKE_BUILD_TYPE=Release
  cmake --build build --config Release
  if [ -x build/run_tests ]; then
    build/run_tests
  elif [ -x build/Release/run_tests ]; then
    build/Release/run_tests
  else
    echo "run_tests not found" >&2
  fi
  if [ -x build/demo ]; then
    build/demo
  elif [ -x build/Release/demo ]; then
    build/Release/demo
  else
    echo "demo not found" >&2
  fi
  exit 0
fi

echo "CMake not found, trying direct compiler invocation"

if command -v g++ >/dev/null 2>&1; then
  g++ -std=c++17 -O2 tests/test_all.cpp -o run_tests
  g++ -std=c++17 -O2 -DBACKEND_MAIN project1.cpp -o demo
  ./run_tests
  ./demo
  exit 0
elif command -v clang++ >/dev/null 2>&1; then
  clang++ -std=c++17 -O2 tests/test_all.cpp -o run_tests
  clang++ -std=c++17 -O2 -DBACKEND_MAIN project1.cpp -o demo
  ./run_tests
  ./demo
  exit 0
else
  echo "No C++ compiler found. Please install g++, clang++, or CMake." >&2
  exit 1
fi

