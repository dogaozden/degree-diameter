#!/bin/bash
# Card c6 (round 6): (7,10), ORBIT "3 2 1", 150 s per seed, timeout 250, up to 5 seeds per group.
# New seeds 101..105: odd seed plain, even seed ORBW=3. A group stops at its first best=0; the solution is
# checked with build_haar2.py and the driver goes on to the next group.
B=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin
C=/home/user/degree-diameter/research/squads/r6/c6
BUILD=/home/user/degree-diameter/research/frontier/build_haar2.py
SUM=$C/summary.txt
cd $C || exit 1
CARD_GROUPS=(
"g1_sl17_229|sl 17 229"
"g2_prod_sl5_sl9_13|prod sl 5 sl 9 13"
"g3_psl131_1|psl 131 1"
)
echo "start $(date +%T)" >> $SUM
for g in "${CARD_GROUPS[@]}"; do
  tag=${g%%|*}; grp=${g#*|}
  for k in 1 2 3 4 5; do
    seed=$((100 + k))
    if [ $((seed % 2)) -eq 0 ]; then W=3; else W=""; fi
    if [ -n "$W" ]; then export ORBW=$W; else unset ORBW; fi
    log=$C/${tag}_s${seed}.log; out=$C/${tag}_s${seed}.txt
    start=$(date +%s)
    ORBIT="3 2 1" timeout 250 nice -n 10 $B/haar_sym 7 10 150 $seed 8 $out $grp > $log 2>&1
    el=$(( $(date +%s) - start ))
    best=$(grep -o 'best=[0-9]*' $log | tail -1 | cut -d= -f2)
    [ -z "$best" ] && best=NORESULT
    chk=$(grep -c 'full diameter check: OK' $log)
    info=$(grep -m1 -o 'Fix[^,;]*' $log)
    echo "$tag [$grp] seed=$seed ORBW=${W:-0} best=$best check_ok=$chk elapsed=${el}s $info" >> $SUM
    if [ "$best" = NORESULT ] && [ "$el" -lt 20 ]; then echo "ABORT: early failure, see $log" >> $SUM; exit 1; fi
    if [ "$best" = 0 ] && [ -s "$out" ]; then
      echo "SOLVED $tag seed=$seed -> $out" >> $SUM
      python3 $BUILD $out > $C/${tag}_s${seed}.build.log 2>&1
      echo "build $tag seed=$seed: $(grep -m1 -E 'VALID' $C/${tag}_s${seed}.build.log)  [$(date +%T)]" >> $SUM
      break
    fi
  done
done
unset ORBW
echo "done $(date +%T)" >> $SUM
