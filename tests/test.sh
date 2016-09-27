./Main tests/test1.inp tests/test1.out
cat tests/test1.inp | ./Main > tests/test1_2.out
./Main -u tests/test1.inp tests/test1_u.out
./Main -r tests/test1.inp tests/test1_3.out
./Main.exe -yr ./tests/test1.inp | z3 -in -smt2 > tests/test1_z.out
./Main.exe -yr ./tests/test2.inp | z3 -in -smt2 > tests/test2_z.out
git diff --stat tests
