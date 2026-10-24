#!/bin/bash
# Squad r6 card c5: (8,9), ORBIT "3 2 2", 300 s per seed.
# Group 1: psl 23 109, seeds 3..7 (odd plain, even ORBW=3). If it solves, stop there.
# Group 2: psl 17 271, seeds 1..3 (plain; ORBW=3 for a seed after a previous seed ended at 1 or 2).
B=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin
DIR=/home/user/degree-diameter/research/squads/r6/c5
BUILD=/home/user/degree-diameter/research/frontier/build_haar2.py
SUM=$DIR/summary.txt
cd "$DIR" || exit 1

# run_group TAG "SEED:ORBW ..." GROUP-ARGS...   ORBW is 0 (plain), 3, or adapt.
# Returns 0 when a seed solves (after build_haar2.py), 1 otherwise.
run_group() {
  local tag=$1 spec=$2
  shift 2
  local item seed orbw out log res best prev=""
  for item in $spec; do
    seed=${item%%:*}
    orbw=${item#*:}
    if [ "$orbw" = "adapt" ]; then
      if [ "$prev" = "1" ] || [ "$prev" = "2" ]; then orbw=3; else orbw=0; fi
    fi
    out=$DIR/${tag}_s${seed}.txt
    log=$DIR/${tag}_s${seed}.log
    rm -f "$out"
    if [ "$orbw" = "0" ]; then unset ORBW; else export ORBW=$orbw; fi
    echo "$(date +%T) start $tag seed=$seed ORBW=$orbw" >> "$SUM"
    ORBIT="3 2 2" timeout 400 nice -n 10 "$B/haar_sym" 8 9 300 "$seed" 8 "$out" "$@" > "$log" 2>&1
    unset ORBW
    res=$(grep '^RESULT' "$log" | tail -1)
    best=$(printf '%s\n' "$res" | grep -o 'best=[0-9]*' | tail -1 | cut -d= -f2)
    echo "$(date +%T) $tag seed=$seed ORBW=$orbw best=${best:-NA} | $res" >> "$SUM"
    prev=$best
    if [ "$best" = "0" ]; then
      echo "$(date +%T) $tag SOLVED seed=$seed; running build_haar2.py" >> "$SUM"
      python3 "$BUILD" "$out" > "$DIR/${tag}_s${seed}.build.txt" 2>&1
      echo "$(date +%T) $tag build exit=$? : $(grep -w VALID "$DIR/${tag}_s${seed}.build.txt" | tail -1) file=$out" >> "$SUM"
      return 0
    fi
  done
  return 1
}

echo "$(date +%T) round 6 card c5 start" >> "$SUM"
if run_group d8D9_psl23_109 "3:0 4:3 5:0 6:3 7:0" psl 23 109; then
  echo "$(date +%T) group psl 23 109 solved; psl 17 271 not run (card)" >> "$SUM"
else
  echo "$(date +%T) group psl 23 109 no solution; starting psl 17 271" >> "$SUM"
  if run_group d8D9_psl17_271 "1:adapt 2:adapt 3:adapt" psl 17 271; then
    echo "$(date +%T) group psl 17 271 solved" >> "$SUM"
  else
    echo "$(date +%T) group psl 17 271 no solution" >> "$SUM"
  fi
fi
echo "$(date +%T) DONE" >> "$SUM"
