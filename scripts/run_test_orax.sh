#!/bin/bash
LLVM_DIR="TODO: Set the path to the LLVM directory"
export LD_LIBRARY_PATH=$LLVM_DIR/lib:$LD_LIBRARY_PATH

ORAX_BIN=$1
FILE=$2
LIB=$3
OPT_FLAGS=$4

clang -c ./${LIB}.c -o ./${LIB}.o
ar rcs ./${LIB}.a ./${LIB}.o
clang -c -emit-llvm ${LIB}.c -o ${LIB}.bc

$ORAX_BIN --stats --simplification=none --theoryof-mode=term --incremental --fuzz-solve ${OPT_FLAGS}  --target-header=./${LIB}.h --target-lib=./${LIB}.a ${FILE}
