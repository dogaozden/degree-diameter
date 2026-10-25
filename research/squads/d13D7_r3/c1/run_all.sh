#!/bin/bash
# squad r3 card c1: sequential hybrid-LNS runs from the 397 set (one run at a time), each 380 s CPU, timeout 900 s wall.
cd /home/user/degree-diameter/research/squads/d13D7_r3/c1
HEX=/home/user/degree-diameter/research/d13D7/hex/hex_q11.bin
INIT=/home/user/degree-diameter/research/squads/d13D7_r2/c6/best_idx.txt
export OMP_NUM_THREADS=1
for spec in "21 11" "22 13" "23 16"; do
  set -- $spec
  seed=$1; cmax=$2
  timeout 900 nice -n 10 ./lns $HEX $INIT run_s$seed.idx 380 $seed 2 $cmax 40 6 0.2 20000 0.3 0.3 300 0.5 20 > run_s$seed.stdout 2> run_s$seed.log
  echo "seed $seed cmax $cmax exit $?" >> runs_status.txt
done
echo ALLDONE >> runs_status.txt
