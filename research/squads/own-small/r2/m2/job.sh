#!/bin/bash
# Card r2-m2 (3,9), D=9: joint base+voltage annealing (salift_s2) at
#   A: p=7 over C37 (n=518), B: p=8 over the 51 groups of order 32 (n=512), C: p=4 over 12 sampled groups of order 64 (n=512).
#   D: top-5 non-valid states restarted (START) with fresh seeds, E: the best non-valid state restarted until the budget.
# Every cost-0 state is converted with best2edges.py and checked with score48 3 9 at once.
# Budget: all wall-clock accounting uses $SECONDS in this shell (no updates inside $(...)).
T=/home/user/degree-diameter/research/squads/own-small/tools
GT=/home/user/degree-diameter/research/squads/own-small/runs/gtxt
W=/home/user/degree-diameter/research/squads/own-small/r2/m2
export D=9
cd $W || exit 1
mkdir -p st valid
LOG=$W/job.log; REC=$W/all.txt; : > $REC; : > valid/results.txt
BUDGET=850; t0=$SECONDS
say()  { echo "$(date -u +%T) t=$((SECONDS-t0)) $*" >> $LOG; }
left() { echo $((BUDGET-(SECONDS-t0))); }
say "job start"

check() {  # check SOLFILE P N TAG: cost-0 state -> edge list -> score48
  local sol=$1 p=$2 N=$3 tag=$4
  python3 -I $T/best2edges.py $GT/g$N.txt $sol valid/$tag.edges > /dev/null 2>&1
  local res; res=$($T/bin/score48 valid/$tag.edges 3 9 2>&1 | tail -1)
  say "CHECK $tag n=$((2*p*N)) $res"
  echo "$tag n=$((2*p*N)) $res" >> valid/results.txt
}

# run P N ID SEED SECS TAG [START]: one gated-free salift_s2 run (the whole job is already gated); records "cost path p N id tag"
run() {
  local p=$1 N=$2 id=$3 seed=$4 secs=$5 tag=$6 st=$7
  local base=$W/st/$tag.sol cost path
  if [ -n "$st" ]; then
    START=$st $T/bin/salift_s2 $p $GT/g$N.txt $id $seed $secs 10 0.3 $base < /dev/null > $W/st/$tag.log 2>&1
    cost=$(head -1 "$st" | awk '{print $4}'); path=$st
  else
    $T/bin/salift_s2 $p $GT/g$N.txt $id $seed $secs 10 0.3 $base < /dev/null > $W/st/$tag.log 2>&1
    cost=999999; path=""
  fi
  if [ -f $base.best ]; then cost=$(head -1 $base.best | awk '{print $4}'); path=$base.best; fi
  if [ -n "$path" ]; then echo "$cost $path $p $N $id $tag" >> $REC; fi
  say "run $tag p=$p N=$N id=$id seed=$seed secs=$secs start=${st:-none} cost=$cost $(tail -1 $W/st/$tag.log)"
  if [ -f $base ]; then check $base $p $N $tag; fi
}

# ---- Phase A: C37, p=7 (n=518), 2 seeds x 60 s
say "PHASE A: C37 p=7"
for s in 1 2; do run 7 37 1 $s 60 c37_s$s ""; done

# ---- Phase B: order 32, p=8 (n=512): all 51 groups, 6 s each, non-abelian first
say "PHASE B: order 32 p=8"
python3 -I $W/abel.py $GT/g32.txt 32 > $W/g32_ab.txt
awk '$2==0{print $1}' $W/g32_ab.txt > $W/order32.txt
awk '$2==1{print $1}' $W/g32_ab.txt >> $W/order32.txt
say "order 32: $(wc -l < $W/order32.txt) groups ($(awk '$2==1' $W/g32_ab.txt | wc -l) abelian)"
while read id; do run 8 32 $id 1 6 p8_g$id ""; done < $W/order32.txt

# ---- Phase C: order 64, p=4 (n=512), 12 random groups of the 267, 5 s each
say "PHASE C: order 64 p=4 sample"
seq 1 267 | awk 'BEGIN{srand(11)}{print rand(), $1}' | sort -k1,1 | head -12 | awk '{print $2}' > $W/g64_sample.txt
while read id; do run 4 64 $id 1 5 p4_g$id ""; done < $W/g64_sample.txt

# ---- Phase D: restart the top 5 non-valid states (fresh seeds, 60 s each)
say "PHASE D: top-5 restarts"
sort -n $REC | awk '$1>0' | head -5 > $W/top5.txt
sd=10
while read cost path p N id tag; do
  sd=$((sd+1)); run $p $N $id $sd 60 r_${tag}_s$sd "$path"
done < $W/top5.txt

# ---- Phase E: keep restarting the best non-valid state until the budget is used
say "PHASE E: restarts of the best state"
while [ "$(left)" -gt 60 ]; do
  secs=$(( $(left) - 30 )); [ $secs -gt 90 ] && secs=90
  read -r cost path p N id tag < <(sort -n $REC | awk '$1>0' | head -1)
  [ -z "$path" ] && { say "no non-valid state left"; break; }
  sd=$((sd+1)); run $p $N $id $sd $secs e_s$sd "$path"
done

say "job done; best records:"
sort -n $REC | head -8 >> $LOG
echo "DONE" >> $LOG
