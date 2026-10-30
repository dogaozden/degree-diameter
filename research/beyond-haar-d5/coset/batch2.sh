#!/bin/bash
# (7,5) coset graphs of products Q x C_k with core-free H in Q; N = 2|G|/h in 1160..1232
P=PermGroup
run() { ./run_group2.sh "$1" "$2" $3 7 60 > /dev/null; }
run a4xc97  "DirectProduct(AlternatingGroup(4), CyclicGroup(IsPermGroup, 97))" 2
run a4xc98  "DirectProduct(AlternatingGroup(4), CyclicGroup(IsPermGroup, 98))" 2
run s4xc49  "DirectProduct(SymmetricGroup(4), CyclicGroup(IsPermGroup, 49))" 2
run s4xc73  "DirectProduct(SymmetricGroup(4), CyclicGroup(IsPermGroup, 73))" 3
run a5xc20  "DirectProduct(AlternatingGroup(5), CyclicGroup(IsPermGroup, 20))" 2
run a5xc29  "DirectProduct(AlternatingGroup(5), CyclicGroup(IsPermGroup, 29))" 3
run a5xc39  "DirectProduct(AlternatingGroup(5), CyclicGroup(IsPermGroup, 39))" 4
run a5xc49  "DirectProduct(AlternatingGroup(5), CyclicGroup(IsPermGroup, 49))" 5
run a5xc58  "DirectProduct(AlternatingGroup(5), CyclicGroup(IsPermGroup, 58))" 6
run psl27xc7  "DirectProduct(PSL(2,7), CyclicGroup(IsPermGroup, 7))" 2
run psl27xc14 "DirectProduct(PSL(2,7), CyclicGroup(IsPermGroup, 14))" 4
run psl27xc21 "DirectProduct(PSL(2,7), CyclicGroup(IsPermGroup, 21))" 6
run psl27xc11 "DirectProduct(PSL(2,7), CyclicGroup(IsPermGroup, 11))" 3
run psl28xc7  "DirectProduct(PSL(2,8), CyclicGroup(IsPermGroup, 7))" 6
run sl23xc73  "DirectProduct(SL(2,3), CyclicGroup(IsPermGroup, 73))" 3
run a5xs3xc10 "DirectProduct(AlternatingGroup(5), SymmetricGroup(3), CyclicGroup(IsPermGroup, 10))" 6
run a5xd20    "DirectProduct(AlternatingGroup(5), DihedralGroup(IsPermGroup, 40))" 4
run s5xd10    "DirectProduct(SymmetricGroup(5), DihedralGroup(IsPermGroup, 20))" 4
echo BATCH2_DONE
