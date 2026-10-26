#!/bin/bash
# phase 2: 4+4 bases (base44_00..04, random 5-regular bipartite multigraphs, max multiplicity 2) over non-abelian groups of orders 49..56
cd /home/user/degree-diameter/research/squads/hunt-d5/r1/a4
export OMP_NUM_THREADS=1 THREADS=1
while ! grep -q P1DONE p1.log; do sleep 10; done
GRP="50:1 50:3 50:4 52:1 52:3 52:4 54:1 54:3 54:4 54:5 54:6 54:7 54:8 54:10 54:11 54:12 54:13 54:14 55:1 56:1 56:3 56:4 56:5 56:6 56:7 56:9 56:10 56:11 56:12"
for gi in $GRP; do
  N=${gi%%:*}; I=${gi##*:}
  T=g${N}_${I}.bin
  [ -f $T ] || timeout 300 nice -n 10 python3 ../../tools/gapgroup.py table $N $I $T >/dev/null 2>&1
  for k in 00 01 02 03 04; do
    OUT=o_p2_${N}_${I}_${k}.v
    R=$(timeout 60 nice -n 10 ../../tools/flift base44_$k.txt $T 5 5 1.5 1 8 $OUT 2>&1 | grep RESULT)
    echo "P2 $N $I $k $R"
  done
done
echo P2DONE
