#!/bin/bash
# phase 1: 2+2 bases (A: multiplicities 1,4,4,1; B: 2,3,3,2) over non-abelian groups of orders 97..110 (+ cyclic controls)
cd /home/user/degree-diameter/research/squads/hunt-d5/r1/a4
export OMP_NUM_THREADS=1 THREADS=1
GRP="98:1 98:3 98:4 100:1 100:3 100:4 100:6 100:7 100:9 100:10 100:11 100:12 100:13 100:14 100:15 102:1 102:2 102:3 104:1 104:3 104:4 104:5 104:6 104:7 104:8 104:10 104:11 104:12 104:13 105:1 106:1 108:1 108:3 108:4 108:6 108:7 108:8 108:9 108:10 108:11 108:13 108:14 108:15 108:16 108:17 108:18 108:19 108:20 108:21 108:22 108:23 108:24 108:25 108:26 108:27 108:28 108:30 108:31 108:32 108:33 108:34 108:36 108:37 108:38 108:39 108:40 110:1 110:2 110:3 110:4 110:5 100:2 108:2"
for gi in $GRP; do
  N=${gi%%:*}; I=${gi##*:}
  T=g${N}_${I}.bin
  [ -f $T ] || timeout 300 nice -n 10 python3 ../../tools/gapgroup.py table $N $I $T >/dev/null 2>&1
  for B in A B; do
    OUT=o_p1_${N}_${I}_${B}.v
    R=$(timeout 60 nice -n 10 ../../tools/flift base2$B.txt $T 5 5 1.5 1 8 $OUT 2>&1 | grep RESULT)
    echo "P1 $N $I $B $R"
  done
done
echo P1DONE
