./Main tests/test1.inp tests/test1.out
cat tests/test1.inp | ./Main > tests/test1_2.out
./Main -u tests/test1.inp tests/test1_u.out
./Main -r tests/test1.inp tests/test1_3.out
git diff --stat tests