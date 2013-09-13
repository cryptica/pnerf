#!/bin/bash

function sort_file {
  cat $1 | sort | sed -e 's/spec\.pl/spec/' >$1.sorted
}

results=( positive negative error timeout )

for benchmark_dir in `find benchmarks -mindepth 1 -maxdepth 1 -type d`; do
  echo "$benchmark_dir"
  for result in "${results[@]}"; do
    sort_file $benchmark_dir/$result".list"
    sort_file $benchmark_dir/$result"-mist.list"
  done
  declare -A sums_tool
  echo -n "         | "
  for rtool in "${results[@]}"; do
    printf "%8s | " $rtool
    sums_tool[$rtool]=0
  done
  echo
  echo -n "---------+-"
  for rtool in "${results[@]}"; do
    echo -n "---------+-"
  done
  echo "---------"
  for rmist in "${results[@]}"; do
    printf "%8s | " $rmist
    sum_mist=0
    for rtool in "${results[@]}"; do
      n=`comm -12 $benchmark_dir/$rtool".list.sorted" $benchmark_dir/$rmist"-mist.list.sorted" | wc -l`
      printf "%8d | " $n
      sum_mist=$((sum_mist + n))
      sums_tool[$rtool]=$((${sums_tool[$rtool]} + n))
    done
    printf "%8d\n" $sum_mist
  done
  echo -n "---------+-"
  for rtool in "${results[@]}"; do
    echo -n "---------+-"
  done
  echo "---------"
  total_sum=0
  echo -n "         | "
  for rtool in "${results[@]}"; do
    printf "%8d | " ${sums_tool[$rtool] }
    total_sum=$((total_sum + ${sums_tool[$rtool] }))
  done
  printf "%8d\n" $total_sum
  echo
done
