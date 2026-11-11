#!/bin/bash
# conflict_lns.sh BEST ITERS : conflict-directed destroy-and-repair on side B (f06).
# Each iteration: score kept orbits with blk (covers blocked by one orbit alone), drop 2-4 of the most blocking
# orbits (random tie-break), regrow with growb for 60 s, keep the result if it has at least as many orbits.
cd "$(dirname "$0")"
EDG=../../data/d16D5_n33792.edges
B=$1; IT=$2
for i in $(seq 1 $IT); do
  n=$(wc -l < $B)
  ./blk $EDG $B score_cur.txt 0 $RANDOM 6 1000 > blk_cur.log 2>&1
  K=$((2 + RANDOM % 3))
  awk 'BEGIN{srand()} {print $2 + rand()*0.5, $1}' score_cur.txt | sort -k1,1nr | head -n $K | awk '{print $2}' > drop_idx.txt
  awk 'NR==FNR{d[$1]=1; next} !((FNR-1) in d)' drop_idx.txt $B > fix_B.txt
  ./growb $EDG fix_B.txt try_B.txt 60 $RANDOM 6 4000 > /dev/null 2>&1
  b=$(wc -l < try_B.txt 2>/dev/null || echo 0)
  if [ "$b" -ge "$n" ]; then cp try_B.txt $B; fi
  echo "$i drop $K [$(tr '\n' ' ' < drop_idx.txt)] sc1max $(sort -k2,2nr score_cur.txt | head -1 | awk '{print $2}'): $n -> $b (best $(wc -l < $B))" >> lns_B.log
done
echo done >> lns_B.log
