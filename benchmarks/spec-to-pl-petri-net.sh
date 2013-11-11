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
    -e "s/^/place('/" \
    -e "s/$/')./"

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
        if [[ $line =~ "->" ]]; then
            n=$((n+1))
            echo "t$n : $line"
        else
            echo $line
        fi
    done
) | \
sed -e '/^[[:blank:]]*$/D' \
    -e 's/^[[:blank:]]*//' \
    -e 's/[[:blank:]]$*//' \
    -e 's/[[:alpha:]_][[:alnum:]_]*[[:blank:]]*>=[[:blank:]]*0[[:blank:]]*//' \
    -e "s/\([[:alpha:]_][[:alnum:]_]*\)[[:blank:]]*>=[[:blank:]]*\([[:digit:]][[:digit:]]*\)/('\1', \2)/g" \
    -e "s/[[:alpha:]_][[:alnum:]_]*'[[:blank:]]*=//g" \
    -e "s/\([[:alpha:]_][[:alnum:]_]*\)[[:blank:]]*+[[:blank:]]*\([[:digit:]][[:digit:]]*\)/('\1', \2)/g" \
    -e "s/\([[:alpha:]_][[:alnum:]_]*\)[[:blank:]]*-[[:blank:]]*\([[:digit:]][[:digit:]]*\)/('\1', -\2)/g" \
    -e "s/\([[:blank:]]*:[[:blank:]]*\(('[[:alpha:]_].*\)->[[:blank:]]*\)/\1\2, /" |\
(
    n=0
    while read line; do
      re="(^.*->.*)\(('[[:alpha:]_][[:alnum:]_]*'), ([[:digit:]]+)\)[[:blank:]]*,[[:blank:]]*(.*)\(\2, (-?[[:digit:]]+)\)[[:blank:]]*,[[:blank:]]*(.*)$"
      while [[ $line =~ $re ]]; do
        out_weight=$((BASH_REMATCH[3] + BASH_REMATCH[5]))
        if [[ $out_weight -gt 0 ]]; then
          line=${BASH_REMATCH[1]}"("${BASH_REMATCH[2]}", "$out_weight"), "${BASH_REMATCH[4]}${BASH_REMATCH[6]}
        else
          line=${BASH_REMATCH[1]}${BASH_REMATCH[4]}${BASH_REMATCH[6]}
        fi
      done
      echo $line
    done
) | \
sed -e 's/,[[:blank:]]*,[[:blank:]]*/, /' \
    -e 's/[[:blank:]]*,[[:blank:]]*/, /g' \
    -e "s/(\('[[:alpha:]_][[:alnum:]_]*'\), 1)/\1/g" \
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
    -e 's/[[:blank:]]*$//' \
    -e '/[[:alnum:]_][[:blank:]]*=[[:blank:]]*0/D' \
    -e "s/\([[:alpha:]_][[:alnum:]_]*\)[[:blank:]]*=[[:blank:]]*\([[:digit:]][[:digit:]_]*\)/init('\1', \2)./" | \
# Example for numbering:
# init(l0>=1
# ---------------------------------
# init(l0, init1).
# cond('(assert (>= init 1))').
(
    n=0
    while read line; do
        if [[ $line =~ (>=[[:blank:]]*[[:digit:]]) ]]; then
            n=$((n+1))
            echo $line | \
              sed -e "s/\([[:alpha:]_][[:alnum:]_]*\)[[:blank:]]*>=[[:blank:]]*\
\([[:digit:]][[:digit:]_]*\)/init('\1', \2).\n\
transition(init$n, [], ['\1'])./"
        else
            echo $line
        fi
    done
)

# target conditions
</tmp/pp-spec.pp \
sed -e '/target/,/invariants/!D' \
    -e '/target/,/EOF/!D' \
    -e '/target/D' \
    -e '/invariants/D' \
    -e '/EOF/D' \
    -e '/^[[:blank:]]*$/D' \
    -e 's/[[:blank:]]*,[[:blank:]]*/,/g' \
    -e "s/\([[:alpha:]_][[:alnum:]_]*\)[[:blank:]]*>=[[:blank:]]*\([[:alnum:]_][[:alnum:]_]*\)/(['\1'],\2)/g" \
    -e 's/^[[:blank:]]*/target([/' \
    -e 's/[[:blank:]]*$/])./'

