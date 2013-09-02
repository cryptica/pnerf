#!/bin/bash

function absolute_path {
    (cd "$(dirname "$1")" && pwd)
}

sysdir=$(absolute_path $0)

# echo
# echo '- Testing construction of petri net N from input file'
# echo
function test-input-file-to-petri-net {
    set -e
    sicstus -l "$sysdir"/src/input-file-to-petri-net.pl -- "$sysdir"/tests/petersons-alg/input-petri-net.pl 2>/dev/null >/tmp/pp-petri-net.pl
    sort "$sysdir"/tests/petersons-alg/pp-petri-net.pl >/tmp/pp-petri-net-exp.pl
    sort /tmp/pp-petri-net.pl >/tmp/pp-petri-net-out.pl
    diff /tmp/pp-petri-net-exp.pl /tmp/pp-petri-net-out.pl
}
if test-input-file-to-petri-net; then
    echo 'petersons-alg/pp-petri-net.pl ... PASS'
else
    echo
    echo 'petersons-alg/pp-petri-net.pl ... FAILED'
    exit 1
fi

# echo
# echo '- Testing construction of constraints C0 for petri net N'
# echo
function test-petri-net-to-constraints {
    set -e
    sicstus -l "$sysdir"/src/petri-net-to-constraints.pl -- "$sysdir"/tests/petersons-alg/pp-petri-net.pl 2>/dev/null >/tmp/constraints-c0.smt2
    sort "$sysdir"/tests/petersons-alg/constraints-c0.smt2 >/tmp/constraints-c0-exp.smt2
    sort /tmp/constraints-c0.smt2 >/tmp/constraints-c0-out.smt2
    diff /tmp/constraints-c0-exp.smt2 /tmp/constraints-c0-out.smt2
}
if test-petri-net-to-constraints; then
    echo 'petersons-alg/constraints-c0.smt2 ... PASS'
else
    echo
    echo 'petersons-alg/constraints-c0.smt2 ... FAILED'
    exit 2
fi

# echo
# echo '- Testing checking of SAT(C)'
# echo
function test-checking-sat {
    if (
        set -e
        z3 -smt2 "$sysdir"/tests/$1 >/tmp/model-out.smt2
        diff "$sysdir"/tests/$2 /tmp/model-out.smt2
        ) then
        echo $2' ... PASS'
    else
        echo $2' ... FAILED'
        exit 3
    fi
}
test-checking-sat petersons-alg/constraints-c0.smt2 petersons-alg/model-a1.smt2
test-checking-sat petersons-alg/constraints-ctheta1.smt2 petersons-alg/model-atheta1.smt2
# test-checking-sat petersons-alg/constraints-c1.smt2 petersons-alg/model-a2.smt2 # TODO: PASS ME
# test-checking-sat petersons-alg/constraints-ctheta2.smt2 petersons-alg/model-atheta2.smt2 # TODO: PASS ME

# echo
# echo '- Testing smt2 model to prolog model'
# echo
function test-smt2-model-to-prolog-model {
    if (
            set -e
            cat "$sysdir"/tests/$1 | "$sysdir"/src/smt2-model-to-prolog-model.sh >/tmp/model.pl
            sort "$sysdir"/tests/$2 | sed '/^$/D' >/tmp/model-exp.pl
            sort  /tmp/model.pl | sed '/^$/D' >/tmp/model-out.pl
            diff /tmp/model-exp.pl /tmp/model-out.pl
        ); then
        echo $2' ... PASS'
    else
        echo $2' ... FAILED'
        exit 4
    fi
}
test-smt2-model-to-prolog-model petersons-alg/model-a1.smt2 petersons-alg/model-a1.pl
test-smt2-model-to-prolog-model petersons-alg/model-atheta1.smt2 petersons-alg/model-atheta1.pl
# test-smt2-model-to-prolog-model petersons-alg/model-a2.smt2 petersons-alg/model-a2.pl # TODO: PASS ME
# test-smt2-model-to-prolog-model petersons-alg/model-atheta2.smt2 petersons-alg/model-atheta2.pl # TODO: PASS ME

# echo
# echo '- Testing construction of trap constraints C_theta for model A'
# echo
function test-trap-constraints {
    set -e
    sicstus -l "$sysdir"/src/trap-constraints.pl -- "$sysdir"/tests/petersons-alg/pp-petri-net.pl "$sysdir"/tests/petersons-alg/model-a1.pl 2>/dev/null >/tmp/constraints-ctheta1.smt2
    sort "$sysdir"/tests/petersons-alg/constraints-ctheta1.smt2 >/tmp/constraints-ctheta1-exp.smt2
    sort /tmp/constraints-ctheta1.smt2 >/tmp/constraints-ctheta1-out.smt2
    diff /tmp/constraints-ctheta1-exp.smt2 /tmp/constraints-ctheta1-out.smt2
}
if test-trap-constraints; then
    echo 'petersons-alg/constraints-ctheta1.pl ... PASS'
else
    echo 'petersons-alg/constraints-ctheta1.pl ... FAILED'
    exit 5
fi
# test-trap-constraints petersons-alg/pp-petri-net.pl petersons-alg/model-a1.pl petersons-alg/constraints-ctheta1.smt2 # TODO: PASS ME
# test-trap-constraints petersons-alg/pp-petri-net.pl petersons-alg/model-a2.pl petersons-alg/constraints-ctheta2.smt2 # TODO: PASS ME

# echo
# echo '- Testing construction of constraint delta for C and A_theta'
# echo
function test-delta-constraint {
    set -e
    sicstus -l "$sysdir"/src/delta-constraint.pl -- "$sysdir"/tests/petersons-alg/model-atheta1.pl 2>/dev/null >/tmp/constraint-delta1-out.smt2
    diff "$sysdir"/tests/petersons-alg/constraint-delta1.smt2 /tmp/constraint-delta1-out.smt2
}
if test-delta-constraint; then
    echo 'petersons-alg/constraint-delta1.smt2 ... PASS'
else
    echo 'petersons-alg/constraint-delta1.smt2 ... FAILED'
    exit 6
fi
# test-delta-constraint petersons-alg/model-atheta1.pl petersons-alg/constraint-delta1.pl # TODO: PASS ME
# test-delta-constraint petersons-alg/model-atheta2.pl petersons-alg/constraint-delta2.pl # TODO: PASS ME

# echo
# echo '- Testing construction of constraints C_n+1 for C_n and A_theta_n'
# echo
function test-succ-constraints {
    set -e
    "$sysdir"/src/succ-constraints.sh "$sysdir"/tests/petersons-alg/constraints-c0.smt2 "$sysdir"/tests/petersons-alg/constraint-delta1.smt2 >/tmp/constraints-c1-out.smt2
    diff "$sysdir"/tests/petersons-alg/constraints-c1.smt2 /tmp/constraints-c1-out.smt2
}
if test-succ-constraints; then
    echo 'petersons-alg/constraints-c1.smt2 ... PASS'
else
    echo 'petersons-alg/constraints-c1.smt2 ... FAILED'
    exit 7
fi
# test-succ-constraints petersons-alg/constraints-c0.smt2 petersons-alg/constraint-delta1.smt2 petersons-alg/constraints-c1.smt2 # TODO: PASS ME
# test-succ-constraints petersons-alg/constraints-c1.smt2 petersons-alg/constraint-delta2.smt2 petersons-alg/constraints-c2.smt2 # TODO: PASS ME