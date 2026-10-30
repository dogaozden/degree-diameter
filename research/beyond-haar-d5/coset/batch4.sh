#!/bin/bash
run() { ./run_group2.sh "$1" "$2" $3 5 30 > /dev/null; }
run c3xa6_h6   "DirectProduct(CyclicGroup(IsPermGroup,3), AlternatingGroup(6))" 6
run c2c2xa6_h8 "DirectProduct(CyclicGroup(IsPermGroup,2), CyclicGroup(IsPermGroup,2), AlternatingGroup(6))" 8
run c4xa6_h8   "DirectProduct(CyclicGroup(IsPermGroup,4), AlternatingGroup(6))" 8
run c2xs6_h8   "DirectProduct(CyclicGroup(IsPermGroup,2), SymmetricGroup(6))" 8
run pgaml29_h8 "AutomorphismGroup(AlternatingGroup(6))" 8
run c5xa6_h10  "DirectProduct(CyclicGroup(IsPermGroup,5), AlternatingGroup(6))" 10
echo BATCH4_DONE
