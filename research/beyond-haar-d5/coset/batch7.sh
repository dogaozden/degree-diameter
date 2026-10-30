#!/bin/bash
# (7,5) push above 1200: h=2 coset graphs (orbit-type Haar graphs allowed) of non-solvable groups, SA 300 s per pair
run() { ./run_group2.sh "$1" "$2" 2 7 300 > /dev/null; echo "done $1" >> logs/batch7.out; }
for i in 61 62; do run sg1260_$i "Image(IsomorphismPermGroup(SmallGroup(1260,$i)))"; done
for i in 13 14 133 134 135 136 137 138; do run sg1320_$i "Image(IsomorphismPermGroup(SmallGroup(1320,$i)))"; done
run agl3_2 "AffGrp(3,2,false)"
run psl27xc8 "DirectProduct(PSL(2,7), CyclicGroup(IsPermGroup,8))"
run psl27xd8 "DirectProduct(PSL(2,7), DihedralGroup(IsPermGroup,8))"
run pgl27xc4 "DirectProduct(PGL(2,7), CyclicGroup(IsPermGroup,4))"
run sl27xc4 "DirectProduct(SL(2,7), CyclicGroup(IsPermGroup,4))"
echo BATCH7_DONE >> logs/batch7.out
