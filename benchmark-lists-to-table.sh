#!/bin/bash

function sort_file {
  cat $1 | \
  sed -e 's/\.pl$//' \
      -e 's/\.spec$//' \
      -e 's/\.tts$//' | \
  sort \
  >$1.sorted
}

results_our_tool=( positive negative dontknow error timeout )
results_other_tool=( positive negative error timeout )

our_tool=pnerf
other_tool=bfc

for benchmark_dir in `find benchmarks -mindepth 1 -maxdepth 1 -type d`; do
  echo "$benchmark_dir"
  for result in "${results_our_tool[@]}"; do
    sort_file $benchmark_dir/$result-$our_tool.list
  done
  for result in "${results_other_tool[@]}"; do
    sort_file $benchmark_dir/$result-$other_tool.list
  done
  echo -n "other\\our| "
  for ((rour=0;rour<${#results_our_tool[@]};rour++)); do
    printf "%8s | " ${results_our_tool[$rour]}
    sums_our_tool[$rour]=0
  done
  echo
  echo -n "---------+-"
  for rour in "${results_our_tool[@]}"; do
    echo -n "---------+-"
  done
  echo "---------"
  for rother in "${results_other_tool[@]}"; do
    printf "%8s | " $rother
    sum_other_tool=0
    for ((rour=0;rour<${#results_our_tool[@]};rour++)); do
      n=`comm -12 $benchmark_dir/${results_our_tool[$rour]}-$our_tool.list.sorted $benchmark_dir/$rother-$other_tool.list.sorted | wc -l`
      printf "%8d | " $n
      sum_other_tool=$((sum_other_tool + n))
      sums_our_tool[$rour]=$((${sums_our_tool[$rour]} + n))
    done
    printf "%8d\n" $sum_other_tool
  done
  echo -n "---------+-"
  for rour in "${results_our_tool[@]}"; do
    echo -n "---------+-"
  done
  echo "---------"
  total_sum=0
  echo -n "         | "
  for ((rour=0;rour<${#results_our_tool[@]};rour++)); do
    printf "%8d | " ${sums_our_tool[$rour]}
    total_sum=$((total_sum + ${sums_our_tool[$rour]}))
  done
  printf "%8d\n" $total_sum
  echo
  N=0
  T_min=-1
  T_max=0
  T_sum=0
  while read T file; do
    N=$((N + 1))
    if [[ $T -gt $T_max ]]; then
      T_max=$T
    fi
    if [[ $T_min -lt 0 || $T -lt $T_min ]]; then
      T_min=$T
    fi
    T_sum=$((T_sum + T))
  done < $benchmark_dir/timing-$our_tool.log
  if [[ $N -gt 0 ]]; then
    T_avg=$((T_sum / N))
    echo -n "Total   time: "
    printf "%.3e\n" $T_sum
    echo -n "Minimal time: "
    printf "%.3e\n" $T_min
    echo -n "Maximal time: "
    printf "%.3e\n" $T_max
    echo -n "Average time: "
    printf "%.3e\n" $T_avg
  fi
  echo
done
