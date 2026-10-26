#!/bin/bash
# Card k3: (3,10), D=10, p=5 base (n = 10N), N = 87..92, all groups per order (non-abelian first).
# Phase 1: screen each group 20 CPU s (seed 1) in ascending N; a cost-0 state is checked and
#          that order is closed (remaining groups of it are skipped).
# Phase 2: restart the 2 lowest-cost states above the largest valid N with new seeds until ~830 s.
T=/home/user/degree-diameter/research/squads/own-small/tools
GT=/home/user/degree-diameter/research/squads/own-small/runs/gtxt
W=/home/user/degree-diameter/research/squads/own-small/r2/k3
BIN=$T/bin/salift_s2
P=5
export D=10
cd $W || exit 1
LOG=$W/job_log.txt
RES=$W/results.txt
: > $RES
echo "start $(date -u +%H:%M:%S)" >> $LOG
VMAX=86

run() { # N id seed secs out [startfile]
  local N=$1 id=$2 seed=$3 secs=$4 out=$5 st=$6
  if [ -n "$st" ] && [ -f "$st" ]; then
    START=$st timeout $((secs + 30)) $BIN $P $GT/g$N.txt $id $seed $secs 10 0.3 $out > $out.log 2>&1
  else
    timeout $((secs + 30)) $BIN $P $GT/g$N.txt $id $seed $secs 10 0.3 $out > $out.log 2>&1
  fi
  grep '^end best' $out.log | tail -1 | awk '{print $3}'
}

check() { # N id solfile : convert and score a cost-0 state
  local N=$1 id=$2 sol=$3
  python3 -I $T/best2edges.py $GT/g$N.txt $sol $sol.edges >> $LOG 2>&1
  $T/bin/score48 $sol.edges 3 10 > $sol.check 2>&1
  local line; line=$(tail -1 $sol.check)
  echo "CHECK N=$N id=$id $line" >> $LOG
  case "$line" in *"RESULT VALID"*) return 0;; *) return 1;; esac
}

order_ids() { # non-abelian groups first (name contains D, Q, S or ':')
  local N=$1
  awk '$1=="G"{print $3, $4}' $GT/g$N.txt > $W/names_$N.txt
  grep -E '[DQS:]' $W/names_$N.txt | awk '{print $1}'
  grep -vE '[DQS:]' $W/names_$N.txt | awk '{print $1}'
}

# Phase 1: screen
for N in 87 88 89 90 91 92; do
  if [ $SECONDS -gt 640 ]; then echo "time: stop screening at N=$N" >> $LOG; break; fi
  for id in $(order_ids $N); do
    if [ $SECONDS -gt 640 ]; then break; fi
    sol=$W/scr_${N}_${id}_1.sol
    c=$(run $N $id 1 20 $sol)
    c=${c:-NA}
    echo "screen N=$N id=$id seed=1 cost=$c t=$SECONDS" >> $LOG
    echo "$c $N $id 1 screen" >> $RES
    if [ "$c" = "0" ]; then
      if check $N $id $sol; then VMAX=$N; echo "VALID n=$((10*N)) N=$N id=$id" >> $LOG; break; fi
    fi
  done
done

# Phase 2: restarts of the 2 best non-valid states above VMAX
cands=$(awk -v vm=$VMAX '$2>vm && $1!="0" && $1!="NA"' $RES | sort -k1,1n -k2,2n | head -2)
echo "phase2 VMAX=$VMAX cands:" >> $LOG; echo "$cands" >> $LOG
k=0
echo "$cands" | while read c N id seed tag; do
  [ -z "$N" ] && continue
  k=$((k + 1))
  remain=$((830 - SECONDS))
  [ $remain -lt 30 ] && break
  per=$((remain / (3 - k)))
  [ $per -lt 30 ] && per=30
  out=$W/push_${N}_${id}_s${k}.sol
  st=$W/scr_${N}_${id}_1.sol.best
  c2=$(run $N $id $((k + 1)) $per $out $st)
  c2=${c2:-NA}
  echo "push N=$N id=$id seed=$((k + 1)) secs=$per cost=$c2 t=$SECONDS" >> $LOG
  echo "$c2 $N $id $((k + 1)) push" >> $RES
  if [ "$c2" = "0" ]; then check $N $id $out && echo "VALID n=$((10*N)) N=$N id=$id (push)" >> $LOG; fi
done
echo "end $(date -u +%H:%M:%S) elapsed=$SECONDS" >> $LOG
