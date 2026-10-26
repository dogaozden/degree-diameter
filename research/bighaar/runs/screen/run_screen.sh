#!/bin/bash
# Random-sample group screen at (16,10), k = 5: RANDORB=M samples per group with FIXF (fixed holes counted separately).
HB=/tmp/claude-0/-home-user-degree-diameter/44b9d801-e3b0-5931-8a0d-00a602da11d2/scratchpad/bin/haar_big3
M=${M:-10}
while read fam p n; do
  [ -z "$fam" ] && continue
  ORBIT="5 3 1" FIXF=1 RANDORB=$M UCAP=1000000 THREADS=1 nice -n 5 timeout 1200 $HB 16 10 0 ${SEED:-5} 1 /dev/null $fam $p $n > screen/rand_${fam}_${p}_${n}.out 2> screen/rand_${fam}_${p}_${n}.log
done
