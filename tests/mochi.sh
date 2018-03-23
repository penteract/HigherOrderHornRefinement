#!/bin/bash
PATH=.:$PATH

OUTFILE="tests/allmochi.out"

cat /dev/null > $OUTFILE

for f in tests/mochi-original-examples/*.inp
do
    echo ${f##*/} >> $OUTFILE
    echo "   Example ML" >> $OUTFILE
    cat ${f%.inp}.ml >> $OUTFILE
    echo >> $OUTFILE
    echo "   Equivalent higher-order Horn clause problem" >> $OUTFILE
    cat $f >> $OUTFILE
    echo >> $OUTFILE
    echo "   After Transformation" >> $OUTFILE
    horus -r $f >> $OUTFILE
    echo >> $OUTFILE
    echo "   Z3 result" >> $OUTFILE
    horus -rzs $f | z3 -smt2 -in >> $OUTFILE
    echo ---------------- >> $OUTFILE
    echo >> $OUTFILE
done
