#!/bin/bash
rm -Rvf build-linux
mkdir build-linux
cd build-linux
{ cmake .. && make -j16; } || { echo "FAILURE"; exit 1; }
#{ cmake .. && make -j16 && core-tests/****; } || { echo "FAILURE"; exit 1; }
echo SUCCESS

# -DGOV=ON
# genhtml coverage.info
# lcov -c  --directory . -o coverage.info
# gcov *.o
# core-tests/CMakeFiles/****.dir$
# cp ../../../core-lib/CMakeFiles/****Lib.dir/* .