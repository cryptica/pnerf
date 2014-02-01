#!/bin/bash

function absolute_path {
    (cd "$(dirname "$1")" && pwd)
}

sysdir=$(absolute_path "$0")

input=$1

sicstus -l "$sysdir"/input-file-to-petri-net.pl -- 0 `pwd`/$input 2>/dev/null >/tmp/petri-net.pl

sicstus -l "$sysdir"/petri-net-to-dot.pl -- /tmp/petri-net.pl 2>/dev/null
