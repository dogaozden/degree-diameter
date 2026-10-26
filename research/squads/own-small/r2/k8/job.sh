#!/bin/bash
# k8: joint base+voltage annealing, (3,10), p=9 (18+18 base vertices), n = 18N, N = 46..50.
# Screen every group of orders 46,47,49,50 for 25 CPU s and N=48 (52 groups) for 6 CPU s (budget),
# then push the lowest-cost state above the best valid order with 45 s START restarts and new seeds.
T=/home/user/degree-diameter/research/squads/own-small/tools
G=/home/user/degree-diameter/research/squads/own-small/runs/gtxt
W=/home/user/degree-diameter/research/squads/own-small/r2/k8
cd "$W" || exit 1
export D=10
P=9
BUD=832
USED=0
VALID_N=45
mkdir -p st
LOG=job.log
: > $LOG
log() { echo "$(date -u +%H:%M:%S) used=$USED $*" >> $LOG; }

# run SECS N ID SEED [START]  -> prints the final best cost; files st/r_N_ID_SEED.sol(.best)
run() {
  local s=$1 N=$2 id=$3 seed=$4 src=$5
  local tag=st/r_${N}_${id}_${seed}
  rm -f $tag.sol $tag.sol.best
  if [ -n "$src" ]; then
    START=$src $T/bin/salift_s2 $P $G/g$N.txt $id $seed $s 10 0.3 $tag.sol > $tag.log 2>&1
  else
    $T/bin/salift_s2 $P $G/g$N.txt $id $seed $s 10 0.3 $tag.sol > $tag.log 2>&1
  fi
  USED=$((USED+s))
  grep '^end best' $tag.log | awk '{print $3}'
}

# first screen of one group: SECS N ID
screen() {
  local c
  c=$(run $1 $2 $3 1 "")
  if [ -f st/r_$2_$3_1.sol.best ]; then cp st/r_$2_$3_1.sol.best st/cur_$2_$3.best; fi
  log "screen N=$2 id=$3 cost=$c"
  if [ "$c" = "0" ] && [ -f st/r_$2_$3_1.sol ]; then check st/r_$2_$3_1.sol $2 $3; fi
}

# check STATE N ID: cost-0 state -> edge list -> score48 ; sets VALID_N when VALID
check() {
  local st=$1 N=$2 id=$3
  python3 -I $T/best2edges.py $G/g$N.txt $st st/e_${N}_${id}.edges
  local res
  res=$($T/bin/score48 st/e_${N}_${id}.edges 3 10 | tail -1)
  log "CHECK N=$N id=$id state=$st : $res"
  if echo "$res" | grep -q "RESULT VALID"; then
    cp $st st/VALID_${N}_${id}.state; cp st/e_${N}_${id}.edges st/VALID_${N}_${id}.edges
    [ $N -gt $VALID_N ] && VALID_N=$N
  else
    mv st/cur_${N}_${id}.best st/bad_${N}_${id}.best 2>/dev/null
  fi
}

# screening: all groups (N=45 skipped: it only ties 810)
for spec in "46 1" "46 2" "47 1" "49 1" "49 2" "50 1" "50 2" "50 3" "50 4" "50 5"; do
  set -- $spec; screen 25 $1 $2
done
for id in $(seq 1 52); do screen 6 48 $id; done

# push: lowest-cost state among orders above VALID_N, 45 s START restarts with new seeds
round=0
while [ $((BUD-USED)) -ge 45 ]; do
  pick=$(for f in st/cur_*.best; do [ -f "$f" ] || continue; read N id p c < "$f"; [ "$N" -gt "$VALID_N" ] && echo "$c $N $id $f"; done | sort -k1,1n -k2,2nr | head -1)
  [ -z "$pick" ] && { log "no candidate above VALID_N=$VALID_N"; break; }
  set -- $pick
  c=$1; N=$2; id=$3; f=$4
  round=$((round+1)); seed=$((100+round))
  c2=$(run 45 $N $id $seed $f)
  nb=st/r_${N}_${id}_${seed}.sol.best
  if [ -f $nb ]; then cp $nb $f; fi
  log "push round=$round N=$N id=$id start=$c end=$c2"
  if [ "$c2" = "0" ] && [ -f st/r_${N}_${id}_${seed}.sol ]; then check st/r_${N}_${id}_${seed}.sol $N $id; fi
done

log "DONE used=$USED valid_N=$VALID_N"
