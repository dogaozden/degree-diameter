#!/bin/bash
# card k4 (3,10), p=6, D=10: joint base+voltage annealing (salift_s2) over every group of N=68..72 (n=816..864).
# Phase A: N=68,70,69,71 (all groups, 20 CPU s, seed 1). Phase B: N=72 (50 groups, 9 CPU s, non-abelian first).
# Phase C: the 3 best cost>0 states restart from their saved state with seed 2 (50 CPU s each).
# Any state at cost 0 is converted (best2edges) and checked with score48 at once.
T=/home/user/degree-diameter/research/squads/own-small/tools
GT=/home/user/degree-diameter/research/squads/own-small/runs/gtxt
W=/home/user/degree-diameter/research/squads/own-small/r2/k4
P=6
export D=10
cd $W || exit 1
mkdir -p runs
LOG=$W/job.log
SCR=$W/screen.txt
: > $SCR
log() { echo "$(date -u +%H:%M:%S) $*" >> $LOG; }

cost_of() { if [ -f "$1" ]; then awk 'NR==1{print $4}' "$1"; else echo 999999; fi; }

check_valid() { # state.best with cost 0 -> edges + score48
  local st=$1 N id c e r
  c=$(cost_of $st)
  if [ "$c" = "0" ]; then
    N=$(awk 'NR==1{print $1}' $st); id=$(awk 'NR==1{print $2}' $st)
    e=$W/valid_N${N}_id${id}_$(basename $st .sol.best).edges
    python3 -I $T/best2edges.py $GT/g$N.txt $st $e >> $LOG 2>&1
    r=$($T/bin/score48 $e 3 10 2>&1 | tail -n 1)
    log "CHECK $st cost0 -> $r"
  fi
}

screen() { # N id secs tag
  local N=$1 id=$2 secs=$3 tag=$4 base=$W/runs/$4
  rm -f $base.sol $base.sol.best
  $T/bin/salift_s2 $P $GT/g$N.txt $id 1 $secs 10 0.3 $base.sol > $base.log 2>&1
  local c=$(cost_of $base.sol.best)
  echo "$c $N $id $base.sol.best" >> $SCR
  log "screen N=$N id=$id cost=$c"
  check_valid $base.sol.best
}

push() { # N id seed secs start.best tag
  local N=$1 id=$2 seed=$3 secs=$4 st=$5 tag=$6 base=$W/runs/$6
  rm -f $base.sol $base.sol.best
  cp $st $base.sol.best
  START=$st $T/bin/salift_s2 $P $GT/g$N.txt $id $seed $secs 10 0.3 $base.sol > $base.log 2>&1
  local c=$(cost_of $base.sol.best)
  echo "$c $N $id $base.sol.best" >> $SCR
  log "push N=$N id=$id seed=$seed cost=$c"
  check_valid $base.sol.best
}

log "start job k4"
# Phase A
for spec in "68:1 3 4 2 5" "70:1 2 3 4" "69:1" "71:1"; do
  N=${spec%%:*}
  for id in ${spec#*:}; do screen $N $id 20 A_N${N}_g${id}; done
done
# Phase B: N=72, abelian groups (2 9 14 18 36 50) last
ab=" 2 9 14 18 36 50 "
for id in $(seq 1 50); do
  case "$ab" in *" $id "*) continue;; esac
  screen 72 $id 9 B_N72_g${id}
done
for id in 2 9 14 18 36 50; do screen 72 $id 9 B_N72_g${id}; done
log "screening done"
# Phase C: restart the 3 best cost>0 states
sort -n $SCR | awk '$1>0' | head -n 3 > $W/top3.txt
cat $W/top3.txt >> $LOG
i=0
while read c N id st; do
  i=$((i+1))
  push $N $id 2 50 $st C${i}_N${N}_g${id}
done < $W/top3.txt
log "job done"
sort -n $SCR > $W/screen_sorted.txt
