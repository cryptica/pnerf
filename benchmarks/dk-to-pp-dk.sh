#!/bin/bash

# name transitions
n=0
while read line; do
    if [[ "$line" =~ ".*->.*" ]]; then
        n=$((n+1))
        echo "t$n : $line"
    else
        echo $line
    fi
done
