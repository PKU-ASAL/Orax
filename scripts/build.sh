BUILD_DIR="TODO: Set the build directory"
LLVM_DIR="TODO: Set the path to the LLVM directory (lib/cmake/llvm)"
echo "Build directory: $BUILD_DIR"
if [ ! -d "$BUILD_DIR" ]; then
    echo "Build directory does not exist. Exiting..."
    exit 1
fi
cd $BUILD_DIR
cmake -G 'Unix Makefiles' -DCMAKE_CXX_STANDARD=17 -DCMAKE_BUILD_TYPE=Debug -DLLVM_DIR=$LLVM_DIR -DLLVM11=ON ..
make -j 32