#!/bin/bash
# c5: fixed-size runs of the reduced search (maximise open classes m for |K| = k lines), start = round-2 29-line clique
cd /home/user/degree-diameter/research/squads/d13D7_r3/c5
for k in 26 27 28 29; do
  OMP_NUM_THREADS=1 timeout 900 nice -n 10 ./red /home/user/degree-diameter/research/d13D7/hex/hex_q11.bin /home/user/degree-diameter/research/d13D7/sets/R320_offsets29_u1-0-0-9-0.txt red_k$k.idx 60 $((100+k)) 7 20000 0.5 $k > log_k$k.txt 2>&1
done
echo finished > fixk_done.txt
