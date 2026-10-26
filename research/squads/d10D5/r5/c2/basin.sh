#!/bin/bash
# basin.sh: card c2 (round 5) iterated reheating. Each step runs c0run.sh (RELAX=2, short anneal, reheat TEMP0)
# from the current start, scores the output with score.sh, and keeps it as the new start if SCORE <= current best.
D=/home/user/degree-diameter/research/squads/d10D5/r5
R4=/home/user/degree-diameter/research/squads/d10D5/r4
W=$D/c2
FS="1 6 5"
ITERS=${ITERS:-2000000}
BUDGET=${BUDGET:-1080}          # wall-clock seconds for the whole loop (card time box)
export THREADS=1 WORKERS=1
T0S=(0.35 0.25 0.18); SWS=(0.03 0.04 0.05 0.06); PTS=(0.6 0.7 0.8)
START=$(date +%s); END=$((START + BUDGET))
cp "$D/S5_c0.lift2.sol" "$W/cur.lift2.sol"
cp "$D/S5_c0.lift2.sol" "$W/best.lift2.sol"
BEST=4; k=0; LOG=$W/basin.log
echo "start best $BEST from $D/S5_c0.lift2.sol, ITERS=$ITERS BUDGET=$BUDGET" | tee -a "$LOG"
while :; do
  now=$(date +%s)
  # one run plus scoring takes about 100 s; stop when the next one would overrun the box
  if [ $((now + 110)) -gt $END ]; then echo "time box reached after $k runs" | tee -a "$LOG"; break; fi
  k=$((k + 1))
  T0=${T0S[$((RANDOM % 3))]}; SW=${SWS[$((RANDOM % 4))]}; PT=${PTS[$((RANDOM % 3))]}
  SD=$((7000 + k))
  rm -f "$W/r$k.sol"
  t0=$(date +%s)
  (cd "$R4" && ./c0run.sh "$D/S5.sol" "$W/cur.lift2.sol" "$FS" "$W/r$k" "$SD" 2 "$ITERS" "$T0" "$SW" "$PT") > "$W/r$k.stdout" 2>&1
  t1=$(date +%s)
  if [ ! -f "$W/r$k.sol" ]; then echo "run $k: no output file (anneal failed)" | tee -a "$LOG"; continue; fi
  line=$(cd "$D" && THREADS=1 WORKERS=1 timeout 300 nice -n 10 ./score.sh "$D/S5.sol" "$W/r$k.sol" "$FS" 2>&1 | grep '^SCORE\|RESULT' | tr '\n' ' ')
  n=$(echo "$line" | awk '/^SCORE/{print $2}')
  case "$n" in ''|*[!0-9]*) n=999 ;; esac
  echo "run $k T0=$T0 SWAPP=$SW PTARG=$PT SEED=$SD ITERS=$ITERS anneal=$((t1 - t0))s: $line" | tee -a "$LOG"
  if [ "$n" -le "$BEST" ]; then
    cp "$W/r$k.sol" "$W/cur.lift2.sol"
    if [ "$n" -lt "$BEST" ]; then echo "  new best $n -> $W/best.lift2.sol" | tee -a "$LOG"; cp "$W/r$k.sol" "$W/best.lift2.sol"; fi
    BEST=$n
  else
    echo "  rejected (start stays at score $BEST)" | tee -a "$LOG"
  fi
  case "$line" in *"RESULT VALID"*) echo "VALID FOUND: $W/r$k.sol" | tee -a "$LOG"; break ;; esac
done
echo "FINAL best SCORE $BEST, file $W/best.lift2.sol, runs $k" | tee -a "$LOG"
