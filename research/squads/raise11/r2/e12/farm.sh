#!/bin/bash
cd /home/user/degree-diameter/research/squads/raise11/r2/e12
B=/home/user/degree-diameter/research/squads/raise11/bin
for s in 5201 5202 5203 5204 5205 5206 5207 5208; do
  ORBIT="3 3 2" THREADS=1 timeout 105 nice -n 10 $B/haar_big0 11 11 95 $s 4 run_257_37_$s.out sl 257 37 > log_$s.txt 2>&1
  echo "seed $s exit $?" >> farm_status.txt
  if grep -q "best=0 " log_$s.txt || grep -q "wrote" log_$s.txt; then echo "SOLVED $s" >> farm_status.txt; break; fi
done
echo FARM_DONE >> farm_status.txt
