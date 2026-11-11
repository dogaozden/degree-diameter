#!/bin/bash
# g09 (round 5, side B, conflict-directed destroy): seed base 10000.
# Each iteration: blk scores kept B-orbits (covers blocked by one orbit alone); drop K in 2..5 top blockers
# (random tie-break); regrow with growb 60 s; keep the result if it has at least as many orbits.
cd "$(dirname "$0")"
R=/home/user/degree-diameter/research/squads/beyond-small
EDG=$R/data/d16D5_n33792.edges
A=$R/r5/startA.txt
B=cur_B.txt; IT=$1
best=$(wc -l < $B)
for i in $(seq 1 $IT); do
  n=$(wc -l < $B)
  SEED=$((10000 + i * 7919 + RANDOM % 1000))
  timeout 100 nice -n 10 ./blk $EDG $B score_cur.txt 0 $SEED 6 1000 > blk_cur.log 2>&1
  K=$((2 + RANDOM % 4))
  awk -v s=$SEED 'BEGIN{srand(s)} {print $2 + rand()*0.5, $1}' score_cur.txt | sort -k1,1nr | head -n $K | awk '{print $2}' > drop_idx.txt
  awk 'NR==FNR{d[$1]=1; next} !((FNR-1) in d)' drop_idx.txt $B > fix_B.txt
  timeout 100 nice -n 10 ./growb $EDG fix_B.txt try_B.txt 60 $((SEED+1)) 6 4000 > growb_$i.log 2>&1
  b=$(wc -l < try_B.txt 2>/dev/null || echo 0)
  if [ "$b" -ge "$n" ] && [ "$b" -gt 0 ]; then cp try_B.txt $B; fi
  echo "$i seed $SEED drop $K [$(tr '\n' ' ' < drop_idx.txt)] sc1max $(sort -k2,2nr score_cur.txt | head -1 | awk '{print $2}'): $n -> $b (cur $(wc -l < $B))" >> lns_B.log
  if [ "$b" -gt "$best" ]; then
    best=$b; cp $B best_sideB_$b.txt
    python3 $R/graphs/build_d17D5_hubs.py best_n_$b.edges --orbits $A best_sideB_$b.txt > build_$b.log 2>&1
    $R/bin/apsp best_n_$b.edges 17 5 > apsp_$b.log 2>&1
    echo "NEW BEST $b: $(tail -1 apsp_$b.log)" >> lns_B.log
  fi
done
echo done >> lns_B.log
