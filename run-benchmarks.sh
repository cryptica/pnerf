#!/bin/bash

for benchmark_dir in `find benchmarks -mindepth 1 -maxdepth 1 -type d`; do
  >$benchmark_dir/positive.list
  >$benchmark_dir/dontknow.list
  >$benchmark_dir/negative.list
  >$benchmark_dir/timeout.list
  >$benchmark_dir/error.list
  >$benchmark_dir/timing.log
  #timeout 10m ./src/main -t $benchmark_dir/timing.log $pl_file | tee $pl_file.out
  for pl_file in `find $benchmark_dir -name "*.pl"`; do
    (
      set -o pipefail;
      timeout 1m ./src/explore-states.sh -d 10 $pl_file | tee $pl_file.out
    )
    result=$?
    if [[ result -eq 0 ]]; then
        echo $pl_file >>$benchmark_dir/positive.list
    elif [[ result -eq 1 ]]; then
        echo $pl_file >>$benchmark_dir/negative.list
    elif [[ result -eq 2 ]]; then
        echo $pl_file >>$benchmark_dir/dontknow.list
    elif [[ result -ge 124 ]]; then
        echo $pl_file >>$benchmark_dir/timeout.list
    else
        echo $pl_file >>$benchmark_dir/error.list
    fi
  done
done
