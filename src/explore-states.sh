#!/bin/bash

function absolute_path {
    (cd "$(dirname "$1")" && pwd)
}

sysdir=$(absolute_path $0)

cat <<EOF
PETRINIZER-EXP: The checker for Petri Nets with state exploration
[$1]
EOF

input=$1

if [ -z $input ]; then
    echo 'ERROR: No input file was given'
    exit 2
fi

if [ ! -e $input ]; then
    echo "ERROR: The file $input does not exist"
    exit 2
fi


echo
echo '* Constructing petri net N from input file'
sicstus -l "$sysdir"/input-file-to-petri-net.pl -- $(realpath $input) 2>/dev/null >/tmp/pp-petri-net.pl
echo
echo '* Starting state space exploration for petri net N'

if ( sicstus -l "$sysdir"/explore-states.pl -- /tmp/pp-petri-net.pl 2>/dev/null); then
    echo 'The petri net satisfies the property!'
    exit 0
else
    echo 'The petri net may not satisfy the property'
    exit 1
fi

