#!/bin/bash
run() { ./run_group2.sh "$1" "$2" 2 7 300 > /dev/null; echo "done $1" >> logs/batch7.out; }
for i in 135 136 137 138; do run sg1320_$i "Image(IsomorphismPermGroup(SmallGroup(1320,$i)))"; done
run psl27xc8 "DirectProduct(PSL(2,7), CyclicGroup(IsPermGroup,8))"
run psl27xd8 "DirectProduct(PSL(2,7), DihedralGroup(IsPermGroup,8))"
run pgl27xc4 "DirectProduct(PGL(2,7), CyclicGroup(IsPermGroup,4))"
echo BATCH7B_DONE >> logs/batch7.out
