#!/bin/bash
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"
echo "Project directory: $PROJECT_DIR"
BENCHMARKS_DIR="$PROJECT_DIR/benchmarks"
if [ ! -d "$BENCHMARKS_DIR" ]; then
    echo "Benchmarks directory does not exist. Exiting..."
    exit 1
fi
BENCHMARKS_RUN_DIR="$PROJECT_DIR/benchmarks-run"
if [ -d "$BENCHMARKS_RUN_DIR" ]; then
    echo "Benchmarks-run directory already exists. Exiting..."
    exit 1
fi
cp -r $BENCHMARKS_DIR $BENCHMARKS_RUN_DIR
python3 benchmark_name_mapping_generator.py $BENCHMARKS_RUN_DIR
echo "Successfully prepared the environment."