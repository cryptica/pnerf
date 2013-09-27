#!/bin/bash

function sort_file {
  cat $1 | sort | sed -e 's/spec\.pl/spec/' >$1.sorted
}

results_tool=( positive negative dontknow error timeout )
results_mist=( positive negative error timeout )

for benchmark_dir in `find benchmarks -mindepth 1 -maxdepth 1 -type d`; do
  echo "$benchmark_dir"
  for result in "${results_tool[@]}"; do
    sort_file $benchmark_dir/$result".list"
  done
  for result in "${results_mist[@]}"; do
    sort_file $benchmark_dir/$result"-mist.list"
  done
  echo -n "         | "
  for ((rtool=0;rtool<${#results_tool[@]};rtool++)); do
    printf "%8s | " ${results_tool[$rtool]}
    sums_tool[$rtool]=0
  done
  echo
  echo -n "---------+-"
  for rtool in "${results_tool[@]}"; do
    echo -n "---------+-"
  done
  echo "---------"
  for rmist in "${results_mist[@]}"; do
    printf "%8s | " $rmist
    sum_mist=0
    for ((rtool=0;rtool<${#results_tool[@]};rtool++)); do
      n=`comm -12 $benchmark_dir/${results_tool[$rtool]}".list.sorted" $benchmark_dir/$rmist"-mist.list.sorted" | wc -l`
      printf "%8d | " $n
      sum_mist=$((sum_mist + n))
      sums_tool[$rtool]=$((${sums_tool[$rtool]} + n))
    done
    printf "%8d\n" $sum_mist
  done
  echo -n "---------+-"
  for rtool in "${results_tool[@]}"; do
    echo -n "---------+-"
  done
  echo "---------"
  total_sum=0
  echo -n "         | "
  for ((rtool=0;rtool<${#results_tool[@]};rtool++)); do
    printf "%8d | " ${sums_tool[$rtool]}
    total_sum=$((total_sum + ${sums_tool[$rtool]}))
  done
  printf "%8d\n" $total_sum
  echo
done
