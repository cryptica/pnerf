#!/bin/bash

function animated_wait {
  chars=('|' '\' '-' '/')
  chars_len=${#chars[@]}
  c=0
  fout="/tmp/animated_wait.out"
  line=1
  echo $*
  $* &
  pid=$!
  trap handle_ctrl_c INT
  tput civis
  while (ps -p $pid >/dev/null); do
    lines_count=`<$fout wc -l`
    tail -n +$line $fout
    line=$((lines_count+1))
    
    echo -n ${chars[$c]}
    c=$(((c+1) % chars_len))
    sleep .2s
    tput cub1
  done
  tput cnorm
}

function handle_ctrl_c {
  tput cnorm
  kill $pid 2>/dev/null
  wait $pid 2>/dev/null
  tail -n +$line $fout
}

animated_wait $*
