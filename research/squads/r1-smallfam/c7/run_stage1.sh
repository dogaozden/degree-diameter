#!/bin/bash
# Card c7 (squad-r1-c7-haiku): (4,9) annealing on groups with tiny abelianization, N in [2486, 3300].
# usage: run_stage1.sh a|b   (a = first four candidates, b = last four); 90 s each, seed 1, one thread.
BIN=/tmp/claude-0/-home-user-degree-diameter/2c3fb1ba-9359-5c52-a9c4-6d81a7db2df8/scratchpad/haar_gen3
CARD=/home/user/degree-diameter/research/squads/r1-smallfam/c7
export THREADS=1
cd "$CARD" || exit 1

run() {  # run NAME SECONDS SEED GROUP-TOKENS... N
  local name=$1 secs=$2 seed=$3
  shift 3
  echo "=== $name seconds=$secs seed=$seed args: $*"
  timeout 130 nice -n 10 "$BIN" 4 9 "$secs" "$seed" 8 "$CARD/sol_${name}_s${seed}.txt" "$@" 2>&1 \
    | tee -a "$CARD/stage1.log" | grep -E 'RESULT'
  echo "exit=${PIPESTATUS[0]}"
}

if [ "$1" = a ]; then
  run psl8_n5   90 1 psl 8 5
  run psl7_n15  90 1 psl 7 15
  run sl5_n21   90 1 sl 5 21
  run pgl7_n8   90 1 pgl 7 8
else
  run psl11_n4  90 1 psl 11 4
  run sl7_n8    90 1 sl 7 8
  run psl13_n3  90 1 psl 13 3
  run agl1_53   90 1 agl1 53 1
fi
