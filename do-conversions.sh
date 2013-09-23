#!/bin/bash

for spec_file in `find benchmarks -name "*.spec"`; do
  echo "$spec_file"
  cat $spec_file | ./benchmarks/spec-to-pl-petri-net.sh > $spec_file.pl
done
