#!/bin/bash
# benchmark (1): time to first solution on meta 251 20 32 1, K=13, TYPES=3 REC=5, SA=1->0.2 cyc 50000, 3 seeds
# (machine load ~11 on 4 cores: CPU seconds are about half of wall seconds, so the wall timeout is generous)
cd /home/user/degree-diameter/research/squads/sd5c-r1/c5
for s in 1 2 3; do
  timeout 900 nice -n 10 env K=13 TYPES=3 REC=5 SECS=120 SA=1 SAT1=0.2 SACYC=50000 SEED=$s MAXSOL=1 STOPFIRST=1 EDGES=/home/user/degree-diameter/research/squads/sd5c-r1/c5/b1_s$s.edges ./fsd_x meta 251 20 32 1 > b1_s$s.txt 2>&1
  echo "seed $s rc=$?" >> bench1.out
done
echo BENCH1_DONE >> bench1.out
