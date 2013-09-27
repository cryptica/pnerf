#!/bin/bash

# Preamble

function absolute_path {
    (cd "$(dirname "$1")" && pwd)
}

sysdir=$(absolute_path $0)

function print_title {
    cat <<EOF
PETRINIZER: The checker for Petri Nets
[$1]
EOF
}

function print_usage {
    cat <<EOF

Usage: $0 [options] input_file
Option list:
 -h | --h | -help | --help    : Prints this help
 -d exploration_depth         : Set exploration depth (default: 0)

EOF
}

# Entry point

print_title "$*"

# parse parameters
depth=0
get_depth=false
for a in $@; do
    case $a in
        -h | --h | -help | --help)
            print_usage
            exit 0
            ;;
        -d)
            get_depth=true
            ;;
        *) if $get_depth ; then
             depth=$a
             get_depth=false
           else
             input=$a
           fi ;;
    esac
done

if [ -z $input ]; then
    echo 'ERROR: No input file was given'
    exit 3
fi

if [ ! -e $input ]; then
    echo "ERROR: The file $input does not exist"
    exit 3
fi

echo
echo '* Constructing petri net N from input file'
sicstus -l "$sysdir"/input-file-to-petri-net.pl -- $(absolute_path $input)/$(basename $input) 2>/dev/null >/tmp/pp-petri-net.pl
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

