#!/bin/bash
# B4: one gate slot, sequential: both checkers on each file given as argument (one file after another).
B=/home/user/degree-diameter/research/squads/d11D10-r2/B4
T=/home/user/degree-diameter/research/squads/d11D10-r2/tools
cd "$B" || exit 1
for f in "$@"; do
  n=$(basename "$f" .txt)
  for c in haarcheck_pq pqcheck; do
    env -u THREADS python3 -I $B/runtimed.py $B/logs/${n}__${c}.log $T/$c "$f"
    echo "$c $n rc=$?" >> $B/logs/chain_small.status
  done
done
echo CHAIN_SMALL_DONE >> $B/logs/chain_small.status
