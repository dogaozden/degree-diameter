#!/bin/sh
# usage: pipe.sh BASE_ITEMS TAG SEED   (insert one Z5 orbit into a m=80 base, then SA repair of top 3)
cd /home/user/degree-diameter/research/squads/handsoff-37/r3g
DUMP=1 timeout 100 nice -n 10 ./grow "$1" 16 5 "$3" 6 3 12 1.5 0.2 300000 out/p_$2 2>&1 | grep -E "min cost|NEW BEST|FINAL|cand|sa:" 
