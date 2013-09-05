#!/bin/bash

function animated_wait {
  fout="/tmp/animated_wait.out"
  line=1
  $* > $fout &
  pid=$!
  trap handle_ctrl_c INT
  tput civis
  while (ps -p $pid >/dev/null); do
    lines_count=`<$fout wc -l`
    tail -n "+$line" $fout
    line=$((lines_count+1))
    for c in '|' '\' '-' '/'; do
      echo -n $c
      sleep .2s
      tput cub1
    done
  done
  tput cnorm
}

function handle_ctrl_c {
  tput cnorm
  kill $pid 2>/dev/null
  wait $pid 2>/dev/null
  tail -n "+$l" $fout
}

animated_wait $*
