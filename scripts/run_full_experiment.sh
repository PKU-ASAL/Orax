#!/bin/bash
ORAX_BIN="TODO: Set the path to the Orax binary"
TIMEOUT=600
echo "Running full experiments"
ORAX_BIN=$ORAX_BIN ./run_orax.py --bench-list fullbench.list  -t ${TIMEOUT}