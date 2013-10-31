#!/bin/bash

cat $1 | \
sed -e '/sat/D' \
    -e '/unsat/D' \
    -e '/(model/D' \
    -e '/^)$/D' | \
tr '\n' '#' | \
sed -e 's/)#/)\
/g' -e 's/#//g' | \
sed -e "s/[[:blank:]]*(define-fun \([[:alpha:]_][[:alnum:]_]*\)[[:blank:]]*()[[:blank:]]*[[:alpha:]_][[:alnum:]_]*[[:blank:]]*\([[:alnum:]._][[:alnum:]._]*\))/assignment('\1', \2)./"
