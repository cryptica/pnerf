#!/bin/bash

cat "$1" | sed -e '/(check-sat)/D' -e '/(get-model)/D'
cat "$2"
echo '(check-sat)'
echo '(get-model)'
