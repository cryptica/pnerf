#!/bin/bash

if ! which mist >/dev/null; then
    echo 'ERROR: Could not locate command mist.'
    exit 1
fi

for benchmark_dir in `find benchmarks -mindepth 2 -maxdepth 2 -type d`; do
  rm -f $benchmark_dir/positive-mist.list
  rm -f $benchmark_dir/negative-mist.list
  for spec_file in `find $benchmark_dir -name "*.spec"`; do
    cat $spec_file | sed '/#.*/D' >/tmp/mist.in
    mist /tmp/mist.in | tee /tmp/mist.out
    if (</tmp/mist.out grep 'EEC concludes safe with the abstraction'); then
        echo $spec_file >>$benchmark_dir/positive-mist.list
    else
        echo $spec_file >>$benchmark_dir/negative-mist.list
    fi
  done
done