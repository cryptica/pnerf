#!/bin/bash

sed -e '/sat/D' \
    -e '/unsat/D' \
    -e '/(model/D' \
    -e '/^)$/D' | \
tr '\n' '#' | \
sed -e 's/)#/)\
/g' -e 's/#//g' | \
sed -e 's/[[:space:]][[:space:]]*/ /g' \
    -e 's/ (define-fun /assignment(/' \
    -e 's/ () [[:alnum:]][[:alnum:]]*/,/' \
    -e 's/)/)./'