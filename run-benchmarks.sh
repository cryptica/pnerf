#!/bin/bash

for benchmark_dir in `find benchmarks -mindepth 1 -maxdepth 1 -type d`; do
  rm -f $benchmark_dir/positive.list
  rm -f $benchmark_dir/negative.list
  rm -f $benchmark_dir/timeout.list
  rm -f $benchmark_dir/error.list
  for pl_file in `find $benchmark_dir -name "*.pl"`; do
    (set -o pipefail; timeout 1m ./src/main $pl_file | tee $pl_file.out)
    result=$?
    if [[ result -eq 0 ]]; then
        echo $pl_file >>$benchmark_dir/positive.list
    elif [[ result -eq 1 ]]; then
        echo $pl_file >>$benchmark_dir/negative.list
    elif [[ result -ge 124 ]]; then
        echo $pl_file >>$benchmark_dir/timeout.list
    else
        echo $pl_file >>$benchmark_dir/error.list
    fi
  done
done
