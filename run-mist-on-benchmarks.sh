#!/bin/bash

if ! which mist >/dev/null; then
    echo 'ERROR: Could not locate command mist.'
    exit 1
fi

#for benchmark_dir in `find benchmarks -mindepth 1 -maxdepth 1 -type d`; do
for benchmark_dir in "benchmarks/found-in-mist-repo"; do
  >$benchmark_dir/positive-mist.list
  >$benchmark_dir/negative-mist.list
  >$benchmark_dir/error-mist.list
  >$benchmark_dir/timeout-mist.list
  >$benchmark_dir/timing-mist.log
  for spec_file in `find $benchmark_dir -name "*.spec"`; do
    echo $spec_file
    cat $spec_file | sed '/#.*/D' >/tmp/mist.in
    T="$(date +%s%N)"
    timeout 1200 mist --tsi /tmp/mist.in 2>&1 >$spec_file.mist.out
    result=$?
    T=$(($(date +%s%N)-T))
    if [[ result -eq 0 ]]; then
      if (<$spec_file.mist.out grep 'TSI concludes safe' >/dev/null); then
          echo $spec_file >>$benchmark_dir/positive-mist.list
          echo "SAFE"
      else
          echo $spec_file >>$benchmark_dir/negative-mist.list
          echo "UNSAFE"
      fi
    elif [[ result -eq 124 || result -eq 137 ]]; then
      echo $spec_file >>$benchmark_dir/timeout-mist.list
      echo "TIMEOUT"
    else
      echo $spec_file >>$benchmark_dir/error-mist.list
      echo "ERROR"
    fi
    echo $T $spec_file >>$benchmark_dir/timing-mist.log
  done
done
