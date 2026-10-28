#!/bin/bash
# runk.sh K SEED SECONDS: one domlocal trial on H(7) points (s = 2), then the independent points-only check.
# Writes out_k<K>_s<SEED>.bin (only if cost 0 is reached) and log_k<K>_s<SEED>.txt; prints the summary line.
K=$1; SEED=$2; SECS=$3
E=/home/user/degree-diameter/research/squads/polylev/r2/e12
cd /home/user/degree-diameter/research/theorems/polylev || exit 1
rm -f $E/out_k${K}_s${SEED}.bin
timeout $((4*SECS)) nice -n 10 bin/domlocal hex/hex_q7.bin points $K 2 $SEED $SECS $E/out_k${K}_s${SEED}.bin > $E/log_k${K}_s${SEED}.txt 2>&1
echo "domlocal exit $? : $(grep -E '^q=' $E/log_k${K}_s${SEED}.txt | tail -1)" 
if [ -f $E/out_k${K}_s${SEED}.bin ]; then
  python3 $E/check_points.py /home/user/degree-diameter/research/theorems/polylev/hex/hex_q7.bin $E/out_k${K}_s${SEED}.bin $K
else
  echo "NO COLOURING WRITTEN for k=$K seed=$SEED (search did not reach cost 0)"
fi
