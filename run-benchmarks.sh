#!/bin/bash

for benchmark_dir in `find benchmarks -mindepth 1 -maxdepth 1 -type d`; do
  rm -f $benchmark_dir/positive.list
  rm -f $benchmark_dir/negative.list
  for pl_file in `find $benchmark_dir -name "*.pl"`; do
    if (set -o pipefail; ./src/main $pl_file | tee $pl_file.out); then
        echo $pl_file >>$benchmark_dir/positive.list
    else
        echo $pl_file >>$benchmark_dir/negative.list
    fi
  done
done
