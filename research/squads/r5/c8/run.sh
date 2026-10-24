#!/bin/bash
# usage: run.sh TAG SEED_FROM SEED_TO GROUP... n     (ORBIT="2 3 0", d=6 D=8, 60 s per seed, stops on solve)
B=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin
CARD=/home/user/degree-diameter/research/squads/r5/c8
TAG=$1; S0=$2; S1=$3; shift 3
GROUP="$*"
cd "$CARD" || exit 1
for s in $(seq "$S0" "$S1"); do
  ORBIT="2 3 0" timeout 160 nice -n 10 "$B/haar_sym" 6 8 60 "$s" 8 "$CARD/${TAG}_s$s.txt" $GROUP > "$CARD/${TAG}_s$s.log" 2>&1
  rc=$?
  best=$(grep -o 'best=[0-9]*' "$CARD/${TAG}_s$s.log" | tail -1)
  echo "$TAG seed $s rc=$rc $best" >> "$CARD/summary.txt"
  if grep -q 'best=0' "$CARD/${TAG}_s$s.log"; then echo "SOLVED $TAG seed $s"; break; fi
done
tail -n 1 "$CARD/summary.txt"
