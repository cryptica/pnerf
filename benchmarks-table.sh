#!/bin/bash

benchmarks=( 'found-in-mist-repo' 'given-by-daniel-kroening' 'ic3-soter' )

methods=( 'safety' 'safety-int' 'refinement' 'refinement-int' 'invariant' 'inv-min' 'inv-ref' 'inv-ref-min' )

timeout=7200

function benchmark_files {
  benchmark=$1
  benchmark_dir='benchmarks/'$benchmark
  in_file=$benchmark_dir'/'$2
  out_file=$benchmark_dir'/'$3
  >$out_file
  while read pl_file; do
    if [[ "$pl_file" =~ ^'#' ]]; then
      echo "Skipping $pl_file"
      continue
    fi
    name=$( echo -n "$pl_file" | \
            sed -e "s/^benchmarks\\/$benchmark\\///" \
                -e 's/\.pl$//' \
                -e 's/\.spec$//' \
                -e 's/\.tts$//')
    echo -n "$name;" | tee -a $out_file
    ./src/print-info-for-net.sh $pl_file | tee -a $out_file
    for method in ${methods[@]}; do
      T="$(date +%s%N)"
      (
        set -o pipefail;
        timeout $timeout ./src/main "-benchmark" "-$method" $pl_file | tee -a $out_file
      )
      result=$?
      T=$(($(date +%s%N)-T))
      if [[ result -eq 124 || result -eq 137 ]]; then
        echo -n "TO;TO;TO;"
      else
        time=$(printf "%4.2f" $(echo "$T / 10^9" | bc -l))
        echo -n "$time;" | tee -a $out_file
      fi
    done
    echo | tee -a $out_file
  done <$in_file
}

for (( b=0;b<${#benchmarks[@]};b++)); do
  benchmark=${benchmarks[$b]}
  echo
  echo "* $benchmark"
  echo
  echo "- positive"
  benchmark_files $benchmark "positive.list" "positive-table.csv"
  echo "- negative"
  benchmark_files $benchmark "negative.list" "negative-table.csv"
done

