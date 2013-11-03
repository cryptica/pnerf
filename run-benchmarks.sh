#!/bin/bash

for benchmark_dir in `find benchmarks -mindepth 1 -maxdepth 1 -type d`; do
  >$benchmark_dir/positive-pnerf.list
  >$benchmark_dir/dontknow-pnerf.list
  >$benchmark_dir/negative-pnerf.list
  >$benchmark_dir/timeout-pnerf.list
  >$benchmark_dir/error-pnerf.list
  >$benchmark_dir/timing-pnerf.log
      #timeout 600 ./src/explore-states.sh -d 0 $pl_file | tee $pl_file.out
  for pl_file in `find $benchmark_dir -name "*.pl"`; do
    T="$(date +%s%N)"
    (
      set -o pipefail;
      timeout 600 ./src/main $pl_file | tee $pl_file.out
    )
    result=$?
    T=$(($(date +%s%N)-T))
    if [[ result -eq 0 ]]; then
        list='positive'
    elif [[ result -eq 1 ]]; then
        list='negative'
    elif [[ result -eq 2 ]]; then
        list='dontknow'
    elif [[ result -eq 124 || result -eq 137 ]]; then
        list='timeout'
    else
        list='error'
    fi
    echo $T $pl_file >>$benchmark_dir/$list-pnerf.list
  done
done
