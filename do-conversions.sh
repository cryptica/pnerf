#!/bin/bash

for spec_file in `find benchmarks -name "*.spec"`; do
  echo "$spec_file"
  cat $spec_file | ./benchmarks/dk-to-pp-dk.sh | \
                   ./benchmarks/pp-dk-to-pl-petri-net.sh > $spec_file.pl
done
