#!/bin/bash
# usage: run.sh TAG SEED_FROM SEED_TO GROUP... n   (ORBIT="3 3 0", d=9 D=8, 150 s per seed, timeout 250)
# odd seeds plain, even seeds ORBW=3. Stops at the first best=0, then runs build_haar2.py on the solution.
B=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin
CARD=/home/user/degree-diameter/research/squads/r6/c8
TAG=$1; S0=$2; S1=$3; shift 3
GROUP="$*"
cd "$CARD" || exit 1
for s in $(seq "$S0" "$S1"); do
  OUT="$CARD/${TAG}_s$s.txt"
  if [ $((s % 2)) -eq 0 ]; then
    ORBIT="3 3 0" ORBW=3 timeout 250 nice -n 10 "$B/haar_sym" 9 8 150 "$s" 8 "$OUT" $GROUP > "$CARD/${TAG}_s$s.log" 2>&1
  else
    ORBIT="3 3 0" timeout 250 nice -n 10 "$B/haar_sym" 9 8 150 "$s" 8 "$OUT" $GROUP > "$CARD/${TAG}_s$s.log" 2>&1
  fi
  rc=$?
  best=$(grep -o 'best=[0-9]*' "$CARD/${TAG}_s$s.log" | tail -1)
  mode=plain; [ $((s % 2)) -eq 0 ] && mode=ORBW3
  echo "$TAG seed $s $mode rc=$rc $best" >> "$CARD/summary.txt"
  if grep -q 'best=0' "$CARD/${TAG}_s$s.log"; then
    echo "SOLVED $TAG seed $s" >> "$CARD/summary.txt"
    timeout 1500 nice -n 10 python3 /home/user/degree-diameter/research/frontier/build_haar2.py "$OUT" > "$CARD/${TAG}_s$s.build.log" 2>&1
    echo "build_haar2 rc=$? $(grep -E 'VALID' "$CARD/${TAG}_s$s.build.log" | tail -1)" >> "$CARD/summary.txt"
    break
  fi
done
echo "DONE $TAG" >> "$CARD/summary.txt"
