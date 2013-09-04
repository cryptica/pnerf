#!/bin/bash

# name transitions
n=0
while read line; do
    if (echo $line | grep -e '->' 2>&1 >/dev/null); then
        n=$((n+1))
        echo "t$n : $line"
    else
        echo $line
    fi
done
