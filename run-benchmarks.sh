#!/bin/bash

for benchmark_dir in `find benchmarks -mindepth 2 -maxdepth 2 -type d`; do
  rm -f $benchmark_dir/positive.list
  rm -f $benchmark_dir/negative.list
  rm -f $benchmark_dir/error.list
  for pl_file in `find $benchmark_dir -name "*.pl"`; do
    if (set -o pipefail; ./src/main $pl_file | tee $pl_file.out); then
        echo $pl_file >>$benchmark_dir/positive.list
    elif grep 'The petri net may not satisfy the property' $pl_file.out 2>&1 >/dev/null; then
        echo $pl_file >>$benchmark_dir/negative.list
    else
        echo $pl_file >>$benchmark_dir/error.list
    fi
  done
done
