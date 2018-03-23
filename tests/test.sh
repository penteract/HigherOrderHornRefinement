#!/bin/bash
PATH=.:$PATH
horus tests/test1.inp tests/test1.out
cat tests/test1.inp | horus > tests/test1_2.out
horus -u tests/test1.inp tests/test1_u.out
horus -r tests/test1.inp tests/test1_3.out
horus -zr ./tests/test1.inp | z3 -in -smt2 > tests/test1_z.out
horus -zr ./tests/test2.inp | z3 -in -smt2 > tests/test2_z.out
horus -r ./tests/guard.inp > tests/guard.out
git diff --stat tests
