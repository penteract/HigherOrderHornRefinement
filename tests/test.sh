#!/bin/bash
PATH=.:$PATH
HigherOrderHornRefinement tests/test1.inp tests/test1.out
cat tests/test1.inp | ./HigherOrderHornRefinement > tests/test1_2.out
HigherOrderHornRefinement -u tests/test1.inp tests/test1_u.out
HigherOrderHornRefinement -r tests/test1.inp tests/test1_3.out
HigherOrderHornRefinement -zr ./tests/test1.inp | z3 -in -smt2 > tests/test1_z.out
HigherOrderHornRefinement -zr ./tests/test2.inp | z3 -in -smt2 > tests/test2_z.out
HigherOrderHornRefinement -r ./tests/guard.inp > tests/guard.out
git diff --stat tests
