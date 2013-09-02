#!/bin/bash

function absolute_path {
    (cd "$(dirname "$1")" && pwd)
}

sysdir=$(absolute_path $0)

echo
echo '- Testing construction of petri net N from input file'
echo
function test-input-file-to-petri-net {
    set -e
    sicstus -l "$sysdir"/src/input-file-to-petri-net.pl -- "$sysdir"/tests/petersons-alg/input-petri-net.pl 2>/dev/null >/tmp/pp-petri-net.pl
    sort "$sysdir"/tests/petersons-alg/pp-petri-net.pl >/tmp/pp-petri-net-exp.pl
    sort /tmp/pp-petri-net.pl >/tmp/pp-petri-net-out.pl
    diff /tmp/pp-petri-net-exp.pl /tmp/pp-petri-net-out.pl
}
if test-input-file-to-petri-net; then
    echo "petersons-alg/input-petri-net.pl ... PASS"
else
    echo "petersons-alg/input-petri-net.pl ... FAILED"
    exit 1
fi


echo
echo '- Testing construction of constraints C0 for petri net N'
echo
function test-petri-net-to-constraints {
    set -e
    sicstus -l "$sysdir"/src/petri-net-to-constraints.pl -- "$sysdir"/tests/petersons-alg/pp-petri-net.pl 2>/dev/null >/tmp/constraints-c0.smt2
    sort "$sysdir"/tests/petersons-alg/constraints-c0.smt2 >/tmp/constraints-c0-exp.smt2
    sort /tmp/constraints-c0.smt2 >/tmp/constraints-c0-out.smt2
    diff /tmp/constraints-c0-exp.smt2 /tmp/constraints-c0-out.smt2
}
if test-petri-net-to-constraints; then
    echo "petersons-alg/pp-petri-net.pl ... PASS"
else
    echo "petersons-alg/pp-petri-net.pl ... FAILED"
    exit 2
fi

echo
echo '- Testing checking of SAT(C)'
echo
function test-checking-satC {
    set -e
    z3 -smt2 "$sysdir"/tests/petersons-alg/constraints-c0.smt2 >/tmp/model-a1.smt2
    diff "$sysdir"/tests/petersons-alg/model-a1.smt2 /tmp/model-a1.smt2
}
if test-checking-satC; then
    echo "petersons-alg/constraints-c0.smt2 ... PASS"
else
    echo "petersons-alg/constraints-c0.smt2 ... FAILED"
    exit 3
fi

echo
echo '- Testing smt2 model to prolog model'
echo
function test-smt2-model-to-prolog-model {
    set -e
    cat "$sysdir"/tests/petersons-alg/model-a1.smt2 | "$sysdir"/src/smt2-model-to-prolog-model.sh >/tmp/model-a1.pl
    # TODO: sort expected and out, then compare
    diff "$sysdir"/tests/petersons-alg/model-a1.pl /tmp/model-a1.pl
}
if test-smt2-model-to-prolog-model; then
    echo "petersons-alg/model-a1.smt2 ... PASS"
else
    echo "petersons-alg/model-a1.smt2 ... FAILED"
    exit 4
fi

echo
echo '- Testing construction of trap conditions C_theta for model A'
echo
function test-trap-conditions {
    set -e
    sicstus -l "$sysdir"/src/trap-conditions.pl -- "$sysdir"/tests/petersons-alg/pp-petri-net.pl "$sysdir"/tests/petersons-alg/model-a1.pl 2>/dev/null >/tmp/constraints-ctheta1.smt2
    sort "$sysdir"/tests/petersons-alg/constraints-ctheta1.smt2 >/tmp/constraints-ctheta1-exp.smt2
    sort /tmp/constraints-ctheta1.smt2 >/tmp/constraints-ctheta1-out.smt2
    diff /tmp/constraints-ctheta1-exp.smt2 /tmp/constraints-ctheta1-out.smt2
}
if test-trap-conditions; then
    echo "petersons-alg/model-a1.pl ... PASS"
else
    echo "petersons-alg/model-a1.pl ... FAILED"
    exit 5
fi
