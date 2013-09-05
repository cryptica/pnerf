#!/bin/bash

sed '/#/D' >/tmp/pp-spec.pp
echo "EOF" >>/tmp/pp-spec.pp

# convert places
</tmp/pp-spec.pp \
sed -e '/vars/,/rules/!D' \
    -e '/vars/D' \
    -e '/rules/D' \
    -e 's/[[:blank:]][[:blank:]]*/\
/g' | \
sed -e '/^[[:blank:]]*$/D' \
    -e 's/^[[:blank:]]*//' \
    -e 's/^/place(/' \
    -e 's/$/)./'

# convert transitions
</tmp/pp-spec.pp \
sed -e '/rules/,/init/!D' \
    -e '/rules/D' \
    -e '/init/D' | \
tr '\n' ' ' | \
sed -e 's/;/, \
/g' | \
(
    n=0
    while read line; do
        if [[ "$line" =~ "->" ]]; then
            n=$((n+1))
            echo "t$n : $line"
        else
            echo $line
        fi
    done
) | \
sed -e '/^[[:blank:]]*$/D' \
    -e 's/^[[:blank:]]*//' \
    -e 's/>=[[:blank:]]*1//g' \
    -e "s/[[:alpha:]][[:alnum:]_]*'[[:blank:]]*=//g" \
    -e 's/+[[:blank:]]*1//g' \
    -e 's/\([[:blank:]]*:[[:blank:]]*\(.*\)->[[:blank:]]*\)/\1\2, /' \
    -e ':loop' \
    -e 's/\(->.*\)\(\b[[:alpha:]][[:alnum:]_]*\b\)[[:blank:]]*,[[:blank:]]*\(.*\)\2[[:blank:]]*-[[:blank:]]*1[[:blank:]]*,[[:blank:]]*/\1\3/' \
    -e 't loop' \
    -e 's/,[[:blank:]]*,[[:blank:]]*/, /' \
    -e 's/[[:blank:]]*,[[:blank:]]*/, /g' \
    -e 's/^/transition(/' \
    -e 's/[[:blank:]]*:[[:blank:]]*/, [/' \
    -e 's/[[:blank:]]*->[[:blank:]]*/], [/' \
    -e 's/,[[:blank:]]*$/])./'

# initial conditions
</tmp/pp-spec.pp \
sed -e '/init/,/target/!D' \
    -e '/init/D' \
    -e '/target/D' | \
tr '\n' ' ' | \
sed -e 's/,[[:blank:]]*/\
/g' \
    -e 's/$/\
/' | \
sed -e '/^[[:blank:]]*$/D' \
    -e 's/^[[:blank:]]*//' \
    -e '/[[:alnum:]_][[:blank:]]*=[[:blank:]]*0/D' \
    -e 's/^/init(/' | \
# Example for numbering:
# init(l0>=1
# ---------------------------------
# init(l0, init1).
# cond('(assert (>= init 1))').
(
    n=0
    while read line; do
        if [[ "$line" =~ (>=[[:blank:]]*1) ]]; then
            n=$((n+1))
            echo $line | sed "s/>=[[:blank:]]*1/, init$n)./"
            echo "cond('(>= init$n 1)')."
        else
            echo $line
        fi
    done
) | \
sed -e 's/[[:blank:]]*=[[:blank:]]*1/)./'

# target conditions
</tmp/pp-spec.pp \
sed -e '/invariants/D' \
    -e '/target/,/EOF/!D' \
    -e '/target/D' \
    -e '/EOF/D' \
    -e 's/,/\
/g' | \
sed -e '/^[[:blank:]]*$/D' \
    -e 's/[[:blank:]]*\([[:alnum:]][[:alnum:]_]*\)[[:blank:]]*\([<>=][<>=]*\)[[:blank:]]*\([[:alnum:]][[:alnum:]_]*\)[[:blank:]]*/\2 \1 \3/g' \
    -e "s/^/cond('(/" \
    -e "s/$/)')./"


