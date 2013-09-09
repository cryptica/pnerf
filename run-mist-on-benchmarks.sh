#!/bin/bash

if ! which mist >/dev/null; then
    echo 'ERROR: Could not locate command mist.'
    exit 1
fi

for benchmark_dir in `find benchmarks -mindepth 2 -maxdepth 2 -type d`; do
  rm -f $benchmark_dir/positive-mist.list
  rm -f $benchmark_dir/negative-mist.list
  rm -f $benchmark_dir/unknown-mist.list
  rm -f $benchmark_dir/timeout-mist.list
  for spec_file in `find $benchmark_dir -name "*.spec"`; do
    echo $spec_file
    cat $spec_file | sed '/#.*/D' >/tmp/mist.in
    if (set -o pipefail; timeout 10s mist --tsi /tmp/mist.in >$spec_file.mist.out); then
      if (<$spec_file.mist.out grep 'TSI concludes safe' >/dev/null); then
          echo $spec_file >>$benchmark_dir/positive-mist.list
          echo "SAFE"
      elif (<$spec_file.mist.out grep 'TSI concludes unsafe' >/dev/null); then
          echo $spec_file >>$benchmark_dir/negative-mist.list
          echo "UNSAFE"
      else
          echo $spec_file >>$benchmark_dir/unknown-mist.list
          echo "UNKNOWN"
      fi
    else
      echo $spec_file >>$benchmark_dir/timeout-mist.list
      echo "TIMEOUT"
    fi
  done
done
