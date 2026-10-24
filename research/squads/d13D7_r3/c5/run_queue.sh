#!/bin/bash
# c5: after the fixed-size reduced runs, the full-graph ILS from the 364 set and from the 397 set (CPU-limited)
cd /home/user/degree-diameter/research/squads/d13D7_r3/c5
until [ -f fixk_done.txt ]; do sleep 15; done
OMP_NUM_THREADS=1 timeout 900 nice -n 10 ./ils /home/user/degree-diameter/research/d13D7/hex/hex_q11.bin /home/user/degree-diameter/research/squads/d13D7_r2/c4/best_idx.txt ils364.idx 240 11 7 10 50000 2 4 0.5 > log_ils364.txt 2>&1
OMP_NUM_THREADS=1 timeout 900 nice -n 10 ./ils /home/user/degree-diameter/research/d13D7/hex/hex_q11.bin /home/user/degree-diameter/research/squads/d13D7_r2/c6/best_idx.txt ils397.idx 240 12 7 10 50000 5 12 0.5 > log_ils397.txt 2>&1
echo finished > queue_done.txt
