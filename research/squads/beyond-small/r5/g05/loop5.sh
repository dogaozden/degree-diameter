#!/bin/bash
# g05: side-A-only annealing (anneal3, empty side-B pool), restarted from the best side-A packing each chunk.
cd "$(dirname "$0")"
E=/home/user/degree-diameter/research/squads/beyond-small/data/d16D5_n33792.edges
for i in $(seq 1 10); do
  rm -f state_g05.txt
  ./anneal3 $E poolA.txt empty_pool1.txt best_A.txt 200 $((6000 + i)) 0.35 0.05 1.5 state_g05.txt best_A.txt > chunk_$i.log 2>&1
  echo "$i K_best=$(wc -l < best_A.txt) $(tail -1 chunk_$i.log)" >> loop5.log
done
echo DONE >> loop5.log
