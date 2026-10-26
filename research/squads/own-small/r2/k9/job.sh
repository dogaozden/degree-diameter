#!/bin/bash
# k9 job: (3,10) joint base+voltage annealing (salift_s2, D=10), p=10..13, goal n > 810.
# Stage 1: screen 23 (p,N,group) candidates at 14 CPU s each (non-abelian first, 3 cyclic/abelian).
# Stage 2: top 6 restart from their best states with new seeds (45 s, T0=4).
# Stage 3: top 2 restart again (110 s, T0=4). Any cost-0 state is converted and checked with score48 at once.
T=/home/user/degree-diameter/research/squads/own-small/tools
GT=/home/user/degree-diameter/research/squads/own-small/runs/gtxt
W=/home/user/degree-diameter/research/squads/own-small/r2/k9
cd $W || exit 1
mkdir -p st push
export D=10
T0_=$(date +%s)
LIMIT=815
LOG=$W/job.log
RES=$W/st/results.txt
: > $RES
log(){ echo "[$(( $(date +%s) - T0_ ))s] $*" >> $LOG; }

verify(){ # tag p N : convert the state and check it with score48
  local st=$W/st/$1.sol; [ -f $st ] || st=$W/st/$1.sol.best
  [ -f $st ] || return
  python3 -I $T/best2edges.py $GT/g$3.txt $st $W/push/$1.edges >/dev/null 2>&1 || { log "convert failed $1"; return; }
  local r; r=$($T/bin/score48 $W/push/$1.edges 3 10 2>&1 | grep RESULT | tail -1)
  log "VERIFY $1 (p=$2 N=$3): ${r:-no RESULT}"
}

# run TAG p N id seed secs T0 [START]; prints the cost
run(){
  local tag=$1 p=$2 N=$3 id=$4 seed=$5 secs=$6 t0=$7 start=$8
  local left=$(( LIMIT - ($(date +%s) - T0_) ))
  if [ $left -lt 15 ]; then log "skip $tag (no time)"; echo 999999; return; fi
  [ $secs -gt $left ] && secs=$left
  local out=$W/st/$tag.sol c
  if [ -n "$start" ]; then
    c=$(START=$start $T/bin/salift_s2 $p $GT/g$N.txt $id $seed $secs $t0 0.3 $out 2>/dev/null | grep '^end best' | awk '{print $3}')
  else
    c=$($T/bin/salift_s2 $p $GT/g$N.txt $id $seed $secs $t0 0.3 $out 2>/dev/null | grep '^end best' | awk '{print $3}')
  fi
  c=${c:-999999}
  log "$tag p=$p N=$N id=$id seed=$seed secs=$secs T0=$t0 start=${start:-none} -> cost $c"
  echo "$c $tag $p $N $id" >> $RES
  if [ "$c" = "0" ]; then verify $tag $p $N; fi
  echo $c
}

# ---- stage 1: screen (non-abelian first)
CANDS="10:42:1 10:42:2 10:42:3 10:42:5 10:44:1 10:44:3 11:38:1 11:39:1 11:40:1 11:40:4 11:40:8 11:40:10 12:34:1 12:36:1 12:36:6 12:36:9 12:36:10 13:32:2 13:32:8 13:32:22 13:34:1 10:41:1 11:37:1 12:34:2"
i=0
for c in $CANDS; do
  i=$((i+1)); IFS=: read p N id <<< "$c"
  run s1_p${p}_N${N}_g${id} $p $N $id $((100+i)) 14 10 >/dev/null
done
log "stage 1 done"

# ---- stage 2: top 6 continue
TOP2=$(sort -n $RES | awk '$1<999999' | head -6)
log "stage 2 from:"; echo "$TOP2" >> $LOG
i=0
while read c tag p N id; do
  [ -z "$tag" ] && continue
  i=$((i+1))
  run ${tag/s1_/s2_} $p $N $id $((200+i)) 45 4 $W/st/$tag.sol.best >/dev/null
done <<< "$TOP2"
log "stage 2 done"

# ---- stage 3: top 2 continue
TOP3=$(grep ' s2_' $RES | sort -n | awk '$1<999999' | head -2)
log "stage 3 from:"; echo "$TOP3" >> $LOG
i=0
while read c tag p N id; do
  [ -z "$tag" ] && continue
  i=$((i+1))
  run ${tag/s2_/s3_} $p $N $id $((300+i)) 110 4 $W/st/$tag.sol.best >/dev/null
done <<< "$TOP3"
log "stage 3 done"

# ---- verify the best states of stages 2 and 3 (cost-0 ones are verified in run)
for tag in $(sort -n $RES | awk '$1<999999 && $1>0 {print $2}' | head -3); do
  p=$(grep " $tag " $RES | head -1 | awk '{print $3}'); N=$(grep " $tag " $RES | head -1 | awk '{print $4}')
  verify $tag $p $N
done
log "job end"
sort -n $RES | head -12 >> $LOG
