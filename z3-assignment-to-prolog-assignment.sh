#!/bin/bash

sed -e '/sat/D' \
    -e '/unsat/D' \
    -e '/(model/D' \
    -e '/^)$/D' | \
tr '\n' ' ' | \
sed 's/)  /)\
/g' | \
sed -e 's/[[:space:]][[:space:]]*/ /g' \
    -e 's/^ //' \
    -e 's/(define-fun \([[:alnum:]][[:alnum:]]*\) () [[:alnum:]][[:alnum:]]* \([[:alnum:]][[:alnum:]]*\))/assignment(\1, \2)./'
