#!/bin/bash
# g03: conflict-directed destroy-and-repair on side A (round 5, card g03; from r4/f06 conflict_lns.sh).
# Side A is run in the swapped graph (Gswap.edges, A side = ids < 16896). Seeds in the range 4000+.
# usage: conflict_lnsA.sh TOTAL_SECS
cd "$(dirname "$0")"
EDG=../../data/Gswap.edges
B=cur_A.txt
cp startA_swap.txt $B
T0=$(date +%s); LIM=$1
best=$(wc -l < $B)
echo "start $best" >> lns_A.log
it=0
while [ $(( $(date +%s) - T0 )) -lt $LIM ]; do
  it=$((it+1))
  n=$(wc -l < $B)
  S1=$((4000 + RANDOM)); S2=$((4000 + RANDOM))
  ./blk $EDG $B score_cur.txt 0 $S1 6 1000 > blk_cur.log 2>&1
  K=$((2 + RANDOM % 3))
  awk 'BEGIN{srand()} {print $2 + rand()*0.5, $1}' score_cur.txt | sort -k1,1nr | head -n $K | awk '{print $2}' > drop_idx.txt
  awk 'NR==FNR{d[$1]=1; next} !((FNR-1) in d)' drop_idx.txt $B > fix_A.txt
  rm -f try_A.txt
  ./growb $EDG fix_A.txt try_A.txt 60 $S2 6 4000 > growb_last.out 2>&1
  b=$(wc -l < try_A.txt 2>/dev/null || echo 0)
  acc=no
  if [ "$b" -ge "$n" ]; then cp try_A.txt $B; acc=yes; fi
  if [ "$b" -gt "$best" ]; then
    best=$b
    awk '{s=""; for(i=1;i<=NF;i++){s=s (i>1?" ":"") ($i+16896)}; print s}' $B > best_sideA_$best.txt
  fi
  echo "$it seeds $S1 $S2 drop $K [$(tr '\n' ' ' < drop_idx.txt)] sc1max $(sort -k2,2nr score_cur.txt | head -1 | awk '{print $2}') : $n -> $b acc=$acc best=$best t=$(( $(date +%s) - T0 ))s" >> lns_A.log
done
echo "done best=$best" >> lns_A.log
