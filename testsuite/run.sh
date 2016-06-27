#!/bin/bash

rm -f *.out
rm -f *.opb

#Script to run all tests

RED='\033[0;31m'
GREEN='\033[0;32m'
NC='\033[0m'
for i in *.src
do
	../autopar $i >/dev/null
	basen=`basename $i .src`
	outname=${basen}.out
	mv output.txt ${outname}
	if  diff -u stdout/${outname} ${outname}
	then
		echo  "${basen}: ${GREEN} PASSED${NC}"
	else
		echo  "${basen}: ${RED} FAILED${NC}"
	fi
done
