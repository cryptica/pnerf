#!/bin/bash

function absolute_path {
    (cd "$(dirname "$1")" && pwd)
}

sysdir=$(absolute_path $0)

tmpdir=/tmp/pnerf-$(date +%s%N)
mkdir $tmpdir

#
# Testing construction of petri net N from input file
#
function test-input-file-to-petri-net {
    if (
      set -e
      sicstus -l "$sysdir"/src/input-file-to-petri-net.pl -- "$sysdir"/tests/$1 2>/dev/null >$tmpdir/pp-petri-net.pl
      sort "$sysdir"/tests/$2 >$tmpdir/pp-petri-net-exp.pl
      sort $tmpdir/pp-petri-net.pl >$tmpdir/pp-petri-net-out.pl
      diff $tmpdir/pp-petri-net-exp.pl $tmpdir/pp-petri-net-out.pl
    ); then
      echo $2' ... PASS'
    else
      echo $2' ... FAILED'
      exit 1
    fi
}
test-input-file-to-petri-net petersons-alg/input-petri-net.pl petersons-alg/pp-petri-net.pl
test-input-file-to-petri-net cyclic-net/input-petri-net.pl cyclic-net/pp-petri-net.pl
test-input-file-to-petri-net empty-trap-net/input-petri-net.pl empty-trap-net/pp-petri-net.pl

#
# Testing construction of constraints C0 for petri net N
#
function test-petri-net-to-constraints {
    if (
      set -e
      sicstus -l "$sysdir"/src/petri-net-to-constraints.pl -- "$sysdir"/tests/$1 2>/dev/null >$tmpdir/constraints-c0.smt2
      sort "$sysdir"/tests/$2 >$tmpdir/constraints-c0-exp.smt2
      sort $tmpdir/constraints-c0.smt2 >$tmpdir/constraints-c0-out.smt2
      diff $tmpdir/constraints-c0-exp.smt2 $tmpdir/constraints-c0-out.smt2
    ); then
      echo $2' ... PASS'
    else
      echo $2' ... FAILED'
      exit 2
    fi
}
test-petri-net-to-constraints petersons-alg/pp-petri-net.pl petersons-alg/constraints-c0.smt2
test-petri-net-to-constraints cyclic-net/pp-petri-net.pl cyclic-net/constraints-c0.smt2
test-petri-net-to-constraints empty-trap-net/pp-petri-net.pl empty-trap-net/constraints-c0.smt2

#
# Testing checking of SAT(C)
#
function test-checking-sat {
    if (
        set -e
        z3 -smt2 "$sysdir"/tests/$1 >$tmpdir/model-out.smt2
        diff "$sysdir"/tests/$2 $tmpdir/model-out.smt2
        ); then
        echo $2' ... PASS'
    else
        echo $2' ... FAILED'
        exit 3
    fi
}
test-checking-sat petersons-alg/constraints-c0.smt2 petersons-alg/model-a1.smt2
test-checking-sat petersons-alg/constraints-c1.smt2 petersons-alg/model-a2.smt2
test-checking-sat petersons-alg/constraints-c2.smt2 petersons-alg/model-a3.smt2
test-checking-sat petersons-alg/constraints-ctheta1.smt2 petersons-alg/model-atheta1.smt2
test-checking-sat petersons-alg/constraints-ctheta2.smt2 petersons-alg/model-atheta2.smt2
test-checking-sat cyclic-net/constraints-c0.smt2 cyclic-net/model-a1.smt2
test-checking-sat cyclic-net/constraints-c1.smt2 cyclic-net/model-a2.smt2
test-checking-sat cyclic-net/constraints-ctheta1.smt2 cyclic-net/model-atheta1.smt2
test-checking-sat cyclic-net/constraints-ctheta-prime1.smt2 cyclic-net/model-atheta-prime1.smt2
test-checking-sat empty-trap-net/constraints-c0.smt2 empty-trap-net/model-a1.smt2
test-checking-sat empty-trap-net/constraints-c1.smt2 empty-trap-net/model-a2.smt2
test-checking-sat empty-trap-net/constraints-c2.smt2 empty-trap-net/model-a3.smt2
test-checking-sat empty-trap-net/constraints-ctheta1.smt2 empty-trap-net/model-atheta1.smt2
test-checking-sat empty-trap-net/constraints-ctheta2.smt2 empty-trap-net/model-atheta2.smt2
test-checking-sat empty-trap-net/constraints-ctheta-prime1.smt2 empty-trap-net/model-atheta-prime1.smt2
test-checking-sat empty-trap-net/constraints-ctheta-prime2.smt2 empty-trap-net/model-atheta-prime2.smt2

#
# Testing smt2 model to prolog model
#
function test-smt2-model-to-prolog-model {
    if (
            set -e
            cat "$sysdir"/tests/$1 | "$sysdir"/src/smt2-model-to-prolog-model.sh >$tmpdir/model.pl
            sort "$sysdir"/tests/$2 | sed '/^$/D' >$tmpdir/model-exp.pl
            sort  $tmpdir/model.pl | sed '/^$/D' >$tmpdir/model-out.pl
            diff $tmpdir/model-exp.pl $tmpdir/model-out.pl
        ); then
        echo $2' ... PASS'
    else
        echo $2' ... FAILED'
        exit 4
    fi
}
test-smt2-model-to-prolog-model petersons-alg/model-a1.smt2 petersons-alg/model-a1.pl
test-smt2-model-to-prolog-model petersons-alg/model-a2.smt2 petersons-alg/model-a2.pl
test-smt2-model-to-prolog-model petersons-alg/model-atheta1.smt2 petersons-alg/model-atheta1.pl
test-smt2-model-to-prolog-model petersons-alg/model-atheta2.smt2 petersons-alg/model-atheta2.pl
test-smt2-model-to-prolog-model cyclic-net/model-a1.smt2 cyclic-net/model-a1.pl
test-smt2-model-to-prolog-model cyclic-net/model-atheta-prime1.smt2 cyclic-net/model-atheta-prime1.pl
test-smt2-model-to-prolog-model empty-trap-net/model-a1.smt2 empty-trap-net/model-a1.pl
test-smt2-model-to-prolog-model empty-trap-net/model-a2.smt2 empty-trap-net/model-a2.pl
test-smt2-model-to-prolog-model empty-trap-net/model-atheta-prime1.smt2 empty-trap-net/model-atheta-prime1.pl
test-smt2-model-to-prolog-model empty-trap-net/model-atheta-prime2.smt2 empty-trap-net/model-atheta-prime2.pl

#
# Testing construction of trap constraints C_theta for model A
#
function test-trap-constraints {
    if (
            set -e
            sicstus -l "$sysdir"/src/refinement-methods/trap-constraints.pl -- "$sysdir"/tests/$1 "$sysdir"/tests/$2 2>/dev/null >$tmpdir/constraints-ctheta.smt2
            sort "$sysdir"/tests/$3 >$tmpdir/constraints-ctheta-exp.smt2
            sort $tmpdir/constraints-ctheta.smt2 >$tmpdir/constraints-ctheta-out.smt2
            diff $tmpdir/constraints-ctheta-exp.smt2 $tmpdir/constraints-ctheta-out.smt2
        ); then
        echo $3' ... PASS'
    else
        echo $3' ... FAILED'
        exit 5
    fi    
}
test-trap-constraints petersons-alg/pp-petri-net.pl petersons-alg/model-a1.pl petersons-alg/constraints-ctheta1.smt2
 test-trap-constraints petersons-alg/pp-petri-net.pl petersons-alg/model-a2.pl petersons-alg/constraints-ctheta2.smt2
test-trap-constraints cyclic-net/pp-petri-net.pl cyclic-net/model-a1.pl cyclic-net/constraints-ctheta1.smt2
test-trap-constraints empty-trap-net/pp-petri-net.pl empty-trap-net/model-a1.pl empty-trap-net/constraints-ctheta1.smt2
test-trap-constraints empty-trap-net/pp-petri-net.pl empty-trap-net/model-a2.pl empty-trap-net/constraints-ctheta2.smt2

#
# Testing construction of constraint delta for A_theta
#
function test-delta-constraint {
    if (
            set -e
            sicstus -l "$sysdir"/src/refinement-methods/trap-delta-constraint.pl -- "$sysdir"/tests/$1 "$sysdir"/tests/$2 2>/dev/null >$tmpdir/constraint-delta-out.smt2
            diff "$sysdir"/tests/$3 $tmpdir/constraint-delta-out.smt2
        ); then
        echo $3' ... PASS'
    else
        echo $3' ... FAILED'
        exit 6
    fi
}
test-delta-constraint petersons-alg/model-atheta1.pl petersons-alg/pp-petri-net.pl petersons-alg/constraint-delta1.smt2
test-delta-constraint petersons-alg/model-atheta2.pl petersons-alg/pp-petri-net.pl petersons-alg/constraint-delta2.smt2

#
# Testing construction of constraints C_n+1 for C_n and A_theta_n
#
function test-succ-constraints {
    if (
            set -e
            "$sysdir"/src/succ-constraints.sh "$sysdir"/tests/$1 "$sysdir"/tests/$2 >$tmpdir/constraints-c-out.smt2
            diff "$sysdir"/tests/$3 $tmpdir/constraints-c-out.smt2
        ); then
        echo $3' ... PASS'
    else
        echo $3' ... FAILED'
        exit 7
    fi
}
test-succ-constraints petersons-alg/constraints-c0.smt2 petersons-alg/constraint-delta1.smt2 petersons-alg/constraints-c1.smt2
test-succ-constraints petersons-alg/constraints-c1.smt2 petersons-alg/constraint-delta2.smt2 petersons-alg/constraints-c2.smt2
test-succ-constraints cyclic-net/constraints-c0.smt2 cyclic-net/constraint-delta-prime1.smt2 cyclic-net/constraints-c1.smt2
test-succ-constraints empty-trap-net/constraints-c0.smt2 empty-trap-net/constraint-delta1.smt2 empty-trap-net/constraints-c1.smt2
test-succ-constraints empty-trap-net/constraints-c1.smt2 empty-trap-net/constraint-delta2.smt2 empty-trap-net/constraints-c2.smt2

#
# Testing construction of subnet trap constraints C_theta for model A
#
function test-subnet-trap-constraints {
    if (
            set -e
            sicstus -l "$sysdir"/src/refinement-methods/subnet-trap-constraints.pl -- "$sysdir"/tests/$1 "$sysdir"/tests/$2 2>/dev/null >$tmpdir/constraints-ctheta-prime.smt2
            sort "$sysdir"/tests/$3 >$tmpdir/constraints-ctheta-prime-exp.smt2
            sort $tmpdir/constraints-ctheta-prime.smt2 >$tmpdir/constraints-ctheta-prime-out.smt2
            diff $tmpdir/constraints-ctheta-prime-exp.smt2 $tmpdir/constraints-ctheta-prime-out.smt2
        ); then
        echo $3' ... PASS'
    else
        echo $3' ... FAILED'
        exit 8
    fi    
}
test-subnet-trap-constraints cyclic-net/pp-petri-net.pl cyclic-net/model-a1.pl cyclic-net/constraints-ctheta-prime1.smt2

#
# Testing construction of subnet constraint delta for N and A_theta
#
function test-subnet-trap-delta-constraint {
    if (
            set -e
            sicstus -l "$sysdir"/src/refinement-methods/subnet-trap-delta-constraint.pl -- "$sysdir"/tests/$1 "$sysdir"/tests/$2 2>/dev/null >$tmpdir/constraint-delta-out.smt2
            diff "$sysdir"/tests/$3 $tmpdir/constraint-delta-out.smt2
        ); then
        echo $3' ... PASS'
    else
        echo $3' ... FAILED'
        exit 9
    fi
}
test-subnet-trap-delta-constraint cyclic-net/pp-petri-net.pl cyclic-net/model-atheta-prime1.pl cyclic-net/constraint-delta-prime1.smt2

#
# Testing construction of empty trap constraints C_theta for model A
#
function test-empty-trap-constraints {
    if (
            set -e
            sicstus -l "$sysdir"/src/refinement-methods/empty-trap-constraints.pl -- "$sysdir"/tests/$1 "$sysdir"/tests/$2 2>/dev/null >$tmpdir/constraints-ctheta-prime.smt2
            sort "$sysdir"/tests/$3 >$tmpdir/constraints-ctheta-prime-exp.smt2
            sort $tmpdir/constraints-ctheta-prime.smt2 >$tmpdir/constraints-ctheta-prime-out.smt2
            diff $tmpdir/constraints-ctheta-prime-exp.smt2 $tmpdir/constraints-ctheta-prime-out.smt2
        ); then
        echo $3' ... PASS'
    else
        echo $3' ... FAILED'
        exit 8
    fi    
}
test-empty-trap-constraints empty-trap-net/pp-petri-net.pl empty-trap-net/model-a1.pl empty-trap-net/constraints-ctheta-prime1.smt2
test-empty-trap-constraints empty-trap-net/pp-petri-net.pl empty-trap-net/model-a2.pl empty-trap-net/constraints-ctheta-prime2.smt2

#
# Testing construction of empty trap constraint delta for N and A_theta
#
function test-empty-trap-delta-constraint {
    if (
            set -e
            sicstus -l "$sysdir"/src/refinement-methods/empty-trap-delta-constraint.pl -- "$sysdir"/tests/$1 "$sysdir"/tests/$2 2>/dev/null >$tmpdir/constraint-delta-out.smt2
            diff "$sysdir"/tests/$3 $tmpdir/constraint-delta-out.smt2
        ); then
        echo $3' ... PASS'
    else
        echo $3' ... FAILED'
        exit 9
    fi
}
test-empty-trap-delta-constraint empty-trap-net/pp-petri-net.pl empty-trap-net/model-atheta-prime1.pl empty-trap-net/constraint-delta1.smt2
test-empty-trap-delta-constraint empty-trap-net/pp-petri-net.pl empty-trap-net/model-atheta-prime2.pl empty-trap-net/constraint-delta2.smt2

