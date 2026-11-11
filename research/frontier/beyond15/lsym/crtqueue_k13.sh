#!/bin/bash
# exact (CRT) scans of the n03 pattern [10,2,3,10] (Gray-shape quotient, k = 13) at composite n = 158, 159
cd "$(dirname "$0")/.."
for nl in "158:21 65 67 87 89 97 101 117" "159:10 13 16 28 46 49 97 100"; do n=${nl%%:*}; for l in ${nl#*:}; do
  r=$(EXH=1 ./bin/liftsym ../../squads/beyond15/r4/n03/quot_k13_10_2_3_10.txt ../../squads/beyond15/r4/n03/quot_k13_10_2_3_10.perm $n $l 15 1 1 lsym/out/crt_n03pat_n${n}_l$l 2>/dev/null | grep EXHRESULT)
  echo "n=$n l=$l $r"; done; done
