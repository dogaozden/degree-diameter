#!/bin/bash
# Card c4 (round 6): (d,D)=(9,10), group psl 41 337, ORBIT "3 3 0", 700 s seeds 1 2 3 700, timeout 800.
# Stops at the first seed with best=0.
C=/home/user/degree-diameter/research/squads/r6/c4
B=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin
LOG=$C/summary.txt
ORBIT="3 3 0"
export ORBIT
for SEED in 1 2 3 700; do
  out=$C/psl41_337_orb330_s${SEED}
  echo "start seed=$SEED $(date +%H:%M:%S)" >> $LOG
  timeout 800 nice -n 10 $B/haar_sym 9 10 700 $SEED 8 $out.txt psl 41 337 > $out.log 2>&1
  rc=$?
  best=$(grep '^RESULT' $out.log | grep -o 'best=[0-9]*' | tail -1 | cut -d= -f2)
  [ -z "$best" ] && best=NA
  echo "psl41_337 ORBIT=3,3,0 seed=$SEED rc=$rc best=$best $(grep -o 'fix=[0-9]*' $out.log | tail -1) $(date +%H:%M:%S)" >> $LOG
  if [ "$best" = "0" ]; then
    echo "SOLVED seed $SEED -> $out.txt" >> $LOG
    break
  fi
done
echo "DONE $(date +%H:%M:%S)" >> $LOG
