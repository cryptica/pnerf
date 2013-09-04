rm -f benchmarks/cprover-PN/positive.list
rm -f benchmarks/cprover-PN/negative.list
for f in benchmarks/cprover-PN/*.pl; do
    if (set -o pipefail; ./src/main $f | tee $f.out); then
        echo $f >>benchmarks/cprover-PN/positive.list
    else
        echo $f >>benchmarks/cprover-PN/negative.list
    fi
done
