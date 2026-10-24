#!/bin/bash
# Card r6/c7: (8,10), ORBIT "3 2 2", N ~ 3.9M. Sequential seeds, one process at a time.
# Groups in order: sl 27 x Z199, prod sl 5 x sl 32, prod sl 8 x psl 25. Up to 5 seeds each.
# Odd seeds plain, even seeds ORBW=3. A group stops at the first best=0.
B=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin
D=/home/user/degree-diameter/research/squads/r6/c7
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
  local rc
  if [ "$w" != 0 ]; then
    ORBIT="$orbit" ORBW=$w timeout 250 nice -n 10 "$B/haar_sym" 8 10 150 "$seed" 8 "$base.txt" "$@" > "$base.log" 2>&1
    rc=$?
  else
    ORBIT="$orbit" timeout 250 nice -n 10 "$B/haar_sym" 8 10 150 "$seed" 8 "$base.txt" "$@" > "$base.log" 2>&1
    rc=$?
  fi
  LASTBEST=$(grep -E 'RESULT.*best=' "$base.log" | grep -oE 'best=[0-9]+' | tail -1 | cut -d= -f2)
  local extra=""
  if [ "$LASTBEST" = "0" ]; then
    SOLVED=1
    extra=$(grep -E 'full diameter check|wrote' "$base.log" | tr '\n' ' ')
  fi
  if [ -n "$LASTBEST" ] && [ "$LASTBEST" -lt "$GMIN" ]; then GMIN=$LASTBEST; fi
  [ -z "$LASTBEST" ] && GMIN=-1
  echo "$tag${suffix} | ORBIT=$orbit | seed=$seed | ORBW=${w} | start=$t0 | rc=$rc | best=${LASTBEST:-NA} | $extra" >> "$S"
}

run_group() { # tag orbit group-tokens(n last)
  local tag=$1 orbit=$2; shift 2
  local seed w
  GMIN=999999; SOLVED=0
  for seed in 41 42 43 44 45; do
    w=0; [ $((seed % 2)) -eq 0 ] && w=3
    run_seed "$tag" "$orbit" "$seed" "$w" "$@"
    [ "$LASTBEST" = "0" ] && break
  done
  echo "GROUP $tag ORBIT=$orbit min_best=$GMIN solved=$SOLVED" >> "$S"
}

echo "start $(date +%T)" >> "$S"
run_group sl27_199 "3 2 2" sl 27 199
run_group prod_sl5_sl32 "3 2 2" prod sl 5 sl 32 1
run_group prod_sl8_psl25 "3 2 2" prod sl 8 psl 25 1
echo "end $(date +%T)" >> "$S"
