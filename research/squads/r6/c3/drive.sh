#!/bin/bash
# Squad r6 card c3. Seeds 11..22 of prod psl 5 psl 5 73 (ORBIT 3 2 0, d=6 D=10), 150 s each, timeout 250.
# Odd seeds plain, even seeds ORBW=3. Stops at the first best=0 and runs build_haar2.py on it.
# If nothing solves, seeds 1..4 of psl 13 241 the same way.
B=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin
C=/home/user/degree-diameter/research/squads/r6/c3
BUILD=/home/user/degree-diameter/research/frontier/build_haar2.py
SUM=$C/summary.txt
export ORBIT="3 2 0"
cd "$C" || exit 1
FOUND=""

# one TAG SEED W GROUPARGS...   -> haar_sym 6 10 150 SEED 8 OUT GROUPARGS...
one() {
  local tag=$1 seed=$2 w=$3
  shift 3
  local base=$C/${tag}_s${seed}
  if [ "$w" = "3" ]; then
    ORBW=3 timeout 250 nice -n 10 "$B/haar_sym" 6 10 150 "$seed" 8 "$base.txt" "$@" > "$base.log" 2>&1
  else
    env -u ORBW timeout 250 nice -n 10 "$B/haar_sym" 6 10 150 "$seed" 8 "$base.txt" "$@" > "$base.log" 2>&1
  fi
  local orb res
  orb=$(grep -m1 'mu = ' "$base.log")
  res=$(grep '^RESULT' "$base.log" | tail -1)
  echo "$tag seed=$seed ORBW=$w | ${orb:-no ORBIT line} | ${res:-NO RESULT LINE}" >> "$SUM"
  if grep '^RESULT' "$base.log" | grep -Eq 'best=0( |$)'; then
    return 0
  fi
  return 1
}

# finish TAG SEED: verify a solution with the independent checker
finish() {
  local base=$C/${1}_s${2}
  echo "SOLVED $base.txt" >> "$SUM"
  timeout 900 nice -n 10 python3 "$BUILD" "$base.txt" > "$base.build.log" 2>&1
  echo "build_haar2 $base.txt: $(grep -E 'VALID|INVALID' "$base.build.log" | tail -1)" >> "$SUM"
}

echo "start $(date)" >> "$SUM"
for s in 11 12 13 14 15 16 17 18 19 20 21 22; do
  w=0
  if [ $((s % 2)) -eq 0 ]; then w=3; fi
  if one prod55_73 "$s" "$w" prod psl 5 psl 5 73; then
    finish prod55_73 "$s"
    FOUND=1
    break
  fi
done

if [ -z "$FOUND" ]; then
  for s in 1 2 3 4; do
    w=0
    if [ $((s % 2)) -eq 0 ]; then w=3; fi
    if one psl13_241 "$s" "$w" psl 13 241; then
      finish psl13_241 "$s"
      FOUND=1
      break
    fi
  done
fi
echo "done $(date) found=${FOUND:-none}" >> "$SUM"
