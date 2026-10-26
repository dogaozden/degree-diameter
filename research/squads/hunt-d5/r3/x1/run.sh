#!/bin/bash
# sequential tabu runs, one process at a time (single-threaded machine rule)
cd /home/user/degree-diameter/research/squads/hunt-d5/r3/x1
R=/home/user/degree-diameter/research/squads/hunt-d5
export OMP_NUM_THREADS=1 THREADS=1
for s in 1 2 3; do
  timeout 330 nice -n 10 ./tabu $R/r1/b1/t615_1.bin 7 60 300 $s 10 50 300 out615_s$s.txt "0 206 135 160 343 459 282" > logs/615_s$s.log 2>&1
done
for s in 1 2; do
  timeout 330 nice -n 10 ./tabu $R/r2/c1/tables/g1378_2.bin 9 60 300 $s 10 50 60 out1378_s$s.txt "0 393 357 912 48 1006 387 124 1056" > logs/1378_s$s.log 2>&1
done
echo ALLDONE > logs/done.txt
