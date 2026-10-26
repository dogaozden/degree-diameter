#!/bin/bash
# cyclic-group screen (run once, 1 s per run; results in screen_cyclic.log)
export OMP_NUM_THREADS=1 THREADS=1
cd /home/user/degree-diameter/research/squads/hunt-d5/r1/a3
for N in $(seq 65 75); do for i in $(seq -w 0 12); do b=b$i; timeout 20 nice -n 10 ../../tools/flift bases/$b.txt meta:$N:1:1 5 5 1 $((N*100+10#$i)) 8 runs/cy_${N}_$b.out 2>&1 | grep RESULT | sed "s/^/$b N=$N /" >> screen_cyclic.log; done; done
