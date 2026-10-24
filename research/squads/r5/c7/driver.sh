#!/bin/bash
# Card c7: (8,8) near-miss groups at N = 120,120. Sequential seeds, one process at a time.
B=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin
D=/home/user/degree-diameter/research/squads/r5/c7
BUILD=/home/user/degree-diameter/research/frontier/build_haar2.py
S=$D/summary.txt
cd "$D" || exit 1
unset ORBW

LASTBEST=""
SOLVED=0
GMIN=999999

run_seed() { # tag orbit seed orbw group-tokens(n last)
  local tag=$1 orbit=$2 seed=$3 w=$4; shift 4
  local suffix=""; [ "$w" != 0 ] && suffix="_w$w"
  local base=$D/${tag}${suffix}_s${seed}
  local t0; t0=$(date +%T)
  if [ "$w" != 0 ]; then
    ORBIT="$orbit" ORBW=$w timeout 190 nice -n 10 "$B/haar_sym" 8 8 90 "$seed" 8 "$base.txt" "$@" > "$base.log" 2>&1
  else
    ORBIT="$orbit" timeout 190 nice -n 10 "$B/haar_sym" 8 8 90 "$seed" 8 "$base.txt" "$@" > "$base.log" 2>&1
  fi
  local rc=$?
  LASTBEST=$(grep -E 'RESULT.*best=' "$base.log" | grep -oE 'best=[0-9]+' | tail -1 | cut -d= -f2)
  local ver=""
  if [ "$LASTBEST" = "0" ] && [ -s "$base.txt" ]; then
    ver=$(python3 "$BUILD" "$base.txt" 2>&1 | tail -1)
    SOLVED=1
  fi
  if [ -n "$LASTBEST" ] && [ "$LASTBEST" -lt "$GMIN" ]; then GMIN=$LASTBEST; fi
  [ -z "$LASTBEST" ] && GMIN=-1
  echo "$tag${suffix} | ORBIT=$orbit | seed=$seed | ORBW=${w} | start=$t0 | rc=$rc | best=${LASTBEST:-NA} | $ver" >> "$S"
}

run_group() { # tag orbit group-tokens(n last); 10 seeds, plain/ORBW=3 alternating; stop on solve
  local tag=$1 orbit=$2; shift 2
  local seeds=(21 22 23 24 25 26 27 28 29 30) i=0 seed w
  GMIN=999999; SOLVED=0
  for seed in "${seeds[@]}"; do
    w=0; [ $((i % 2)) -eq 1 ] && w=3
    i=$((i + 1))
    run_seed "$tag" "$orbit" "$seed" "$w" "$@"
    [ "$LASTBEST" = "0" ] && break
  done
  echo "GROUP $tag ORBIT=$orbit min_best=$GMIN solved=$SOLVED" >> "$S"
}

echo "start $(date +%T)" >> "$S"
run_group sl11_91 "3 2 2" sl 11 91
SL_SOLVED=$SOLVED; SL_MIN=$GMIN
run_group pgl11_91 "3 2 2" pgl 11 91
PGL_SOLVED=$SOLVED; PGL_MIN=$GMIN
echo "groups done $(date +%T) sl_solved=$SL_SOLVED sl_min=$SL_MIN pgl_solved=$PGL_SOLVED pgl_min=$PGL_MIN" >> "$S"

if [ "$SL_SOLVED" = 0 ] && [ "$PGL_SOLVED" = 0 ] && [ "$SL_MIN" -ge 6 ] && [ "$PGL_MIN" -ge 6 ]; then
  echo "extras triggered $(date +%T)" >> "$S"
  for orbit in "2 4 0" "4 2 0"; do
    tag=sl11_91_k$(echo $orbit | cut -d' ' -f1)
    GMIN=999999
    for seed in 21 22 23 24; do
      run_seed "$tag" "$orbit" "$seed" 0 sl 11 91
      [ "$LASTBEST" = "0" ] && break
    done
    echo "GROUP $tag ORBIT=$orbit min_best=$GMIN solved=$SOLVED" >> "$S"
    [ "$SOLVED" = 1 ] && break
  done
fi
echo "end $(date +%T)" >> "$S"
