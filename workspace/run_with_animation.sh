#!/bin/bash

function animated_wait {
  tput civis
  while (ps -p $1 >/dev/null); do
    for c in '|' '\' '-' '/'; do
      echo -n $c
      sleep .2s
      tput cub1
    done
  done
  tput cnorm
}

($*) & (animated_wait $!)
