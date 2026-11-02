#!/bin/bash
# n05: longer anneals on the two cost-6 quotient patterns (composite n = 284 k=7, n = 178 k=11)
F=/home/user/degree-diameter/research/frontier/beyond15/lsym
L=$F/qg
D=/home/user/degree-diameter/research/squads/beyond15/r4/n05/long
mkdir -p $D
for s in 11 12 13; do
  THREADS=1 timeout 100 $F/../../bin/liftsym $L/g939593_k7_2_4_3_5.txt $L/g939593_k7_2_4_3_5.perm 284 37 15 45 $s $D/k7_n284_s$s 2>&1 | grep -E "RESULT|EXH|best" | tail -2 | sed "s/^/k7 n284 s$s: /"
  THREADS=1 timeout 100 $F/../../bin/liftsym $L/g447448_k11_5_9_7_10.txt $L/g447448_k11_5_9_7_10.perm 178 39 15 45 $s $D/k11_n178_s$s 2>&1 | grep -E "RESULT|EXH|best" | tail -2 | sed "s/^/k11 n178 s$s: /"
done
echo LONGDONE
