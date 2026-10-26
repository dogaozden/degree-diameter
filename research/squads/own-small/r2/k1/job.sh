#!/bin/bash
# Card k1 (3,10), D=10, p=4 (n = 8N), every group of orders N = 102..110 (n = 816..880).
# Phase 1: screen every group with one salift_s2 run (seed 1; 7 CPU s, cyclic groups 3 s).
# Phase 2: restart the best states from their saved .best (START) with fresh seeds, 45 s each.
#          Ladder: only candidates with N > the largest valid N so far.
# Cost-0 states are converted with best2edges.py and checked with score48 3 10.
T=/home/user/degree-diameter/research/squads/own-small/tools
G=/home/user/degree-diameter/research/squads/own-small/runs/gtxt
W=/home/user/degree-diameter/research/squads/own-small/r2/k1
P=4
export D=10
cd "$W" || exit 1
mkdir -p screen runs valid
LOG=$W/job.log
: > "$LOG"
log() { echo "[${SECONDS}s] $*" >> "$LOG"; }

declare -A COST STATE
MAXVALID=0
VALIDS=""

# $1 = N, $2 = cost-0 state (.sol), $3 = tag
check_valid() {
  local N=$1 st=$2 tag=$3 res n
  n=$((2 * P * N))
  python3 -I "$T/best2edges.py" "$G/g$N.txt" "$st" "valid/$tag.edges" >> "$LOG" 2>&1
  "$T/bin/score48" "valid/$tag.edges" 3 10 > "valid/$tag.check.txt" 2>&1
  res=$(tail -1 "valid/$tag.check.txt")
  log "CHECK $tag n=$n : $res"
  if echo "$res" | grep -q "RESULT VALID"; then
    [ "$N" -gt "$MAXVALID" ] && MAXVALID=$N
    VALIDS="$VALIDS $tag(n=$n)"
  fi
}

# ---------- Phase 1: screen ----------
for N in $(seq 102 110); do
  gf=$G/g$N.txt
  for id in $(awk '$1=="G"{print $3}' "$gf"); do
    name=$(awk -v i="$id" '$1=="G" && $3==i {print $4; exit}' "$gf")
    key="${N}_${id}"
    tag="s${N}_${id}"
    secs=7
    [[ $name =~ ^C[0-9]+$ ]] && secs=3
    if [ "$SECONDS" -gt 620 ]; then log "phase 1 time guard at $tag"; break 2; fi
    "$T/bin/salift_s2" $P "$gf" "$id" 1 $secs 10 0.3 "screen/$tag.sol" > "screen/$tag.log" 2>&1
    c=$(awk '/^end best/{print $3}' "screen/$tag.log")
    [ -z "$c" ] && c=999999
    COST[$key]=$c
    [ -f "screen/$tag.sol.best" ] && STATE[$key]="screen/$tag.sol.best"
    log "screen $tag $name cost=$c"
    if [ -f "screen/$tag.sol" ]; then check_valid "$N" "screen/$tag.sol" "$tag"; fi
  done
done
for key in "${!COST[@]}"; do echo "${COST[$key]} $key"; done | sort -n > screen/summary.txt
log "phase 1 done, maxvalid N=$MAXVALID"

# ---------- Phase 2: restarts, ladder upward ----------
seed=2
while [ "$SECONDS" -lt 800 ]; do
  cand=$(for key in "${!COST[@]}"; do
    N=${key%_*}; c=${COST[$key]}
    [ "$N" -le "$MAXVALID" ] && continue
    [ "$c" -le 0 ] && continue
    [ -n "${STATE[$key]}" ] || continue
    echo "$c $((1000 - N)) $key"
  done | sort -n -k1,1 -k2,2 | head -8 | awk '{print $3}')
  [ -z "$cand" ] && { log "no candidates left"; break; }
  for key in $cand; do
    [ "$SECONDS" -lt 800 ] || break 2
    N=${key%_*}; id=${key#*_}
    [ "$N" -gt "$MAXVALID" ] || continue
    gf=$G/g$N.txt
    tag="r${N}_${id}_s${seed}"
    start=${STATE[$key]}
    START="$start" "$T/bin/salift_s2" $P "$gf" "$id" "$seed" 45 10 0.3 "runs/$tag.sol" > "runs/$tag.log" 2>&1
    c=$(awk '/^end best/{print $3}' "runs/$tag.log")
    [ -z "$c" ] && c=999999
    log "restart $tag from $start end=$c (was ${COST[$key]})"
    if [ -f "runs/$tag.sol" ]; then check_valid "$N" "runs/$tag.sol" "$tag"; fi
    if [ -f "runs/$tag.sol.best" ] && [ "$c" -lt "${COST[$key]}" ]; then
      COST[$key]=$c; STATE[$key]="runs/$tag.sol.best"
    fi
    seed=$((seed + 1))
  done
done

log "DONE maxvalid N=$MAXVALID n=$((2 * P * MAXVALID)) valids:$VALIDS"
for key in "${!COST[@]}"; do echo "${COST[$key]} $key ${STATE[$key]}"; done | sort -n > runs/final_summary.txt
