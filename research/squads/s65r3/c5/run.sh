#!/bin/bash
# card c5 (squad-r3-c5-haiku): anneal (vl, SECS=10) then exact 2-opt (kopt K=2) on runs with cost 1..12.
# Phase 1: every (group, base) once (seed 1). Phase 2: the 4 pairs with the lowest phase-1 cost, more seeds, until the deadline.
R=/home/user/degree-diameter/research/s65
C=/home/user/degree-diameter/research/squads/s65r3/c5
O=$C/out
T0=$(date +%s)
LAUNCH_END=$((T0+1500))   # no new anneal after this
HARD_END=$((T0+1900))     # no kopt after this
G176="sg_176_1 sg_176_7 sg_176_17 sg_176_26 sg_176_10 sg_176_11 sg_176_12 sg_176_21 sg_176_23 sg_176_27 sg_176_8 sg_176_9"
G180="sg_180_1 sg_180_2 sg_180_3 sg_180_13 sg_180_14 sg_180_15 sg_180_16 sg_180_17"
BASES="b22_1 b22_2 b22_3"
SUM=$C/summary.txt
CAND=$C/candidates.txt
: > $SUM 2>/dev/null
touch $CAND

check_sol_block() {  # FILE(with SOL blocks or vl solution) GROUP TAG : export first block, score it
  local F=$1 G=$2 TAG=$3 first=$1.first.sol
  if grep -q '^SOL ' $F; then
    awk 'BEGIN{n=0} /^SOL /{n++} n==1{ if(/^SOL /) sub(/^SOL /,""); print }' $F > $first
  else
    cp $F $first
  fi
  python3 $R/tools/export_lift.py $first $R/groups/sg/$G.txt $first.edges >/dev/null
  local sc=$($R/tools/score65 $first.edges | tr '\n' ' ')
  local ap=$(timeout 600 nice -n 10 $R/tools/apsp $first.edges 6 5 2>/dev/null | grep RESULT | head -1)
  echo "$TAG $G $first.edges :: $sc :: $ap" | tee -a $CAND
  case "$ap" in *VALID*INVALID*|*INVALID*) ;; *VALID*) echo "!!! RECORD CANDIDATE $first.edges" | tee -a $CAND ;; esac
}

run_one() {  # GROUP BASE SEED
  local G=$1 B=$2 S=$3
  local sol=$O/${G}_${B}_s${S}.sol
  local c
  c=$(D=5 SECS=10 SEED=$S OUT=$sol THREADS=1 nice -n 10 timeout 120 $R/tools/vl $R/bases/$B.txt $R/groups/sg/$G.txt 2>/dev/null | grep RESULT | awk '{print $3}')
  local k2=0
  if [ -n "$c" ] && [ "$c" -eq 0 ] 2>/dev/null; then
    check_sol_block $sol $G "COST0"
    k2="cost0"
  elif [ -n "$c" ] && [ "$c" -le 12 ] 2>/dev/null && [ $(date +%s) -lt $HARD_END ]; then
    local rem=$((HARD_END - $(date +%s))); [ $rem -gt 300 ] && rem=300
    timeout $rem nice -n 10 $R/tools/kopt $sol $R/groups/sg/$G.txt 2 5 > $sol.k2 2> $sol.k2err
    k2=$(grep -c '^SOL' $sol.k2)
    if [ "$k2" -gt 0 ]; then check_sol_block $sol.k2 $G "K2"; fi
  fi
  echo "$G $B $S ${c:-NA} $k2" | tee -a $SUM
}

echo "start $(date)"
for G in $G176 $G180; do for B in $BASES; do
  [ $(date +%s) -ge $LAUNCH_END ] && break
  run_one $G $B 1
done; done

# phase 2: 4 lowest pairs by phase-1 cost
TOP=$(awk '$3=="1"{ c=$4; if(c=="NA"||c=="") c=99999; print c, $1, $2 }' $SUM | sort -n | head -4)
echo "top pairs:"; echo "$TOP"
SEED=2
while [ $(date +%s) -lt $LAUNCH_END ]; do
  while read c G B; do
    [ -z "$G" ] && continue
    [ $(date +%s) -ge $LAUNCH_END ] && break 2
    run_one $G $B $SEED
  done <<< "$TOP"
  SEED=$((SEED+1))
done
echo "done $(date)"
