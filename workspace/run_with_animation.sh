#!/bin/bash

function animated_wait {
  $* &
  pid=$!
  trap handle_ctrl_c INT
  tput civis
  while (ps -p $pid >/dev/null); do
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
}

animated_wait $*
