#!/bin/bash
# Card c1 (random-restart baseline): run cover_match sequentially (one process at a time).
# usage: sweep.sh K SEED_FROM SEED_TO        (places 0 and 1, interleaved per seed)
K=$1; S0=$2; S1=$3
CARD=/home/user/degree-diameter/research/squads/c157-r1/c1
LOG=/tmp/claude-0/-home-user-degree-diameter/07637e37-13ff-5912-bf46-48e7ca07985c/scratchpad/c1logs
mkdir -p "$LOG"
cd /home/user/degree-diameter/research/d15D7 || exit 1
ulimit -s unlimited
for s in $(seq "$S0" "$S1"); do
  for PL in 0 1; do
    out="$CARD/K${K}_p${PL}_s${s}.sol"
    line=$(timeout 900 nice -n 10 ./cover_match hex/hex_q11.bin "$K" "$s" 12 "$out" "none${K}.hg" "$PL" 2>>"$LOG/K${K}_p${PL}_s${s}.err" | grep '^RESULT')
    if [ -z "$line" ]; then
      echo "seed=$s place=$PL K=$K FAILED (no RESULT line)" >> "$CARD/results.txt"
      rm -f "$out"
      continue
    fi
    U=$(echo "$line" | sed -E 's/.*unmatched-after-matching ([0-9]+).*/\1/')
    C=$(echo "$line" | sed -E 's/.*leftover cost ([0-9]+).*/\1/')
    echo "seed=$s place=$PL U=$U C=$C | $line" >> "$CARD/results.txt"
  done
done
