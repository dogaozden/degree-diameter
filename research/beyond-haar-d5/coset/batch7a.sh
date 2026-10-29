#!/bin/bash
run() { ./run_group2.sh "$1" "$2" 2 7 300 > /dev/null; echo "done $1" >> logs/batch7.out; }
for i in 61 62; do [ -f logs/sg1260_${i}_h2_d7.r2 ] || run sg1260_$i "Image(IsomorphismPermGroup(SmallGroup(1260,$i)))"; done
for i in 13 14 133 134; do run sg1320_$i "Image(IsomorphismPermGroup(SmallGroup(1320,$i)))"; done
run agl3_2 "AffGrp(3,2,false)"
echo BATCH7A_DONE >> logs/batch7.out
