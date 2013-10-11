#!/bin/bash

for benchmark_dir in `find benchmarks -mindepth 1 -maxdepth 1 -type d`; do
  >$benchmark_dir/positive-pnerf.list
  >$benchmark_dir/dontknow-pnerf.list
  >$benchmark_dir/negative-pnerf.list
  >$benchmark_dir/timeout-pnerf.list
  >$benchmark_dir/error-pnerf.list
  >$benchmark_dir/timing.log
      #timeout 600 ./src/main $pl_file | tee $pl_file.out
  for pl_file in `find $benchmark_dir -name "*.pl"`; do
    T="$(date +%s%N)"
    (
      set -o pipefail;
      timeout 28800 ./src/explore-states.sh -d 100 $pl_file | tee $pl_file.out
    )
    result=$?
    T=$(($(date +%s%N)-T))
    if [[ result -eq 0 ]]; then
        echo $pl_file >>$benchmark_dir/positive-pnerf.list
    elif [[ result -eq 1 ]]; then
        echo $pl_file >>$benchmark_dir/negative-pnerf.list
    elif [[ result -eq 2 ]]; then
        echo $pl_file >>$benchmark_dir/dontknow-pnerf.list
    elif [[ result -eq 124 || result -eq 137 ]]; then
        echo $pl_file >>$benchmark_dir/timeout-pnerf.list
    else
        echo $pl_file >>$benchmark_dir/error-pnerf.list
    fi
    echo $T $pl_file >>$benchmark_dir/timing.log
  done
done
