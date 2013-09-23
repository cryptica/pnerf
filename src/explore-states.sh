#!/bin/bash

function absolute_path {
    (cd "$(dirname "$1")" && pwd)
}

sysdir=$(absolute_path $0)

cat <<EOF
PETRINIZER-EXP: The checker for Petri Nets with state exploration
[$1]
EOF

function print_usage {
    cat <<EOF

Usage: $0 exploration_depth input_file

EOF
}
echo count $#
if [ $# -lt 2 ]; then
    print_usage
    exit 2
fi

depth=$1
input=$2

if [ ! -e $input ]; then
    echo "ERROR: The file $input does not exist"
    exit 2
fi


echo
echo '* Constructing petri net N from input file'
sicstus -l "$sysdir"/input-file-to-petri-net.pl -- $(realpath $input) 2>/dev/null >/tmp/pp-petri-net.pl
echo
echo '* Starting state space exploration for petri net N'

sicstus -l "$sysdir"/explore-states.pl -- $depth /tmp/pp-petri-net.pl 2>/dev/null
result=$?
if [[ result -eq 0 ]]; then
    echo 'The petri net satisfies the property!'
    exit 0
elif [[ result -eq 1 ]]; then
    echo 'The petri does not satisfy the property'
    exit 1
else
    echo 'The petri net may not satisfy the property'
    exit 2
fi

