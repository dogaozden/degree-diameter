#!/bin/bash
# usage: runseeds.sh p n seeds...
B=/home/user/degree-diameter/research/squads/raise11/bin
cd /home/user/degree-diameter/research/squads/raise11/r2/e07
p=$1; n=$2; shift 2
for S in "$@"; do
  ORBIT="3 3 1" THREADS=1 timeout 100 nice -n 10 $B/haar_big0 10 11 70 $S 4 run_sl_${p}_${n}_$S.out sl $p $n > log_$S.txt 2>&1
  echo "seed $S exit $?" >> seeds_done.txt
  grep RESULT log_$S.txt >> results.txt
done
echo ALLDONE >> seeds_done.txt
