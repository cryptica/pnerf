#!/bin/bash

function absolute_path {
    (cd "$(dirname "$1")" && pwd)
}

sysdir=$(absolute_path $0)

tmpdir=/tmp

input=$1

cp $(absolute_path $input)/$(basename $input) $tmpdir/input-petri-net.pl

sicstus -l "$sysdir"/input-file-to-petri-net.pl -- 0 $tmpdir/input-petri-net.pl 2>/dev/null >$tmpdir/pp-petri-net.pl
sicstus -l "$sysdir"/print-info-for-net.pl -- $tmpdir/pp-petri-net.pl 2>/dev/null

