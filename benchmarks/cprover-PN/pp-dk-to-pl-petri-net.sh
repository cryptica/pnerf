#!/bin/bash

sed '/#/D' >/tmp/pp-dk.pp
echo "EOF" >>/tmp/pp-dk.pp

# convert places
</tmp/pp-dk.pp \
sed -e '/vars/,/rules/!D' \
    -e '/vars/D' \
    -e '/rules/D' \
    -e '/^[[:blank:]]*$/D' \
    -e 's/ /\
/g' | \
sed -e 's/^/place(/' \
    -e 's/$/)./'

# convert transitions
</tmp/pp-dk.pp \
sed -e '/rules/,/init/!D' \
    -e '/rules/D' \
    -e '/init/D' | \
tr '\n' ' ' | \
sed -e 's/;/, \
/g' | \
sed -e '/^[[:blank:]]*$/D' \
    -e 's/^ */transition(/' \
    -e 's/>=1//g' \
    -e "s/[[:alnum:]]*'=[[:alnum:]]*-1, //g" \
    -e "s/[[:alnum:]]*'=//g" \
    -e 's/+1//g' \
    -e 's/ : /, [/' \
    -e 's/ -> /], [/' \
    -e 's/, $/])./'

# initial conditions
</tmp/pp-dk.pp \
sed -e '/init/,/target/!D' \
    -e '/init/D' \
    -e '/target/D' \
    -e 's/, */\
/g' | \
sed -e '/^[[:blank:]]*$/D' \
    -e '/[[:alnum:]]=0/D' \
    -e 's/^/init(/' | \
# Example for numbering:
# init(l0>=1
# ---------------------------------
# init(l0, init1).
# cond('(assert (>= init 1))').
(
    n=0
    while read line; do
        if echo $line | grep '>=1' >/dev/null; then
            n=$((n+1))
            echo $line | sed "s/>=1/, init$n)./"
            echo "cond('(>= init$n 1)')."
        else
            echo $line
        fi
    done
) | \
sed -e 's/=1/)./'

# target conditions
</tmp/pp-dk.pp \
sed -e '/target/,/EOF/!D' \
    -e '/target/D' \
    -e '/EOF/D' \
    -e 's/,/\
/g' | \
sed -e 's/\([[:alnum:]]*\)>=/>= \1 /g' \
    -e "s/^/cond('(/" \
    -e "s/$/)')./"


