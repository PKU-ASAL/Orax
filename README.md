# Orax
1. Configure the environment
    * LLVM 11.0.0
        * Other versions may work but are not guaranteed
2. Build the project
    * Adjust the build script `scripts/build.sh` to match your environment
```shell
cd scripts
./build.sh
```
3. Run the experiments
    * Adjust the scripts `scripts/run_full_experiment.sh` and `scripts/run_test_orax.sh` to match your environment
    * The results will be saved as `orax_{timestamp}.csv` in the current working directory
```shell
cd scripts
./prepare_experiment.sh
./run_full_experiment.sh
```