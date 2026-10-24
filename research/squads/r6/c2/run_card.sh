#!/bin/bash
# Round 6 card c2: (8,8), group pgl 11 x Z_91 (N=120120), ORBIT="3 2 2", 90 s per seed, seeds 41..56.
# Odd seeds plain, even seeds ORBW=3. Stops at the first best=0 and runs build_haar2.py on the solution.
B=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin
C=/home/user/degree-diameter/research/squads/r6/c2
SUM=$C/summary.txt
cd /home/user/degree-diameter/research/squads || exit 1
echo "start $(date +%T)" >> $SUM
for seed in $(seq 41 56); do
  if [ $((seed % 2)) -eq 0 ]; then W="ORBW=3"; tag=pgl11_91_w3; else W=""; tag=pgl11_91; fi
  log=$C/${tag}_s${seed}.log; out=$C/${tag}_s${seed}.txt
  start=$(date +%s)
  env ORBIT="3 2 2" $W timeout 190 nice -n 10 $B/haar_sym 8 8 90 $seed 8 $out pgl 11 91 > $log 2>&1
  el=$(( $(date +%s) - start ))
  best=$(grep -o 'best=[0-9]*' $log | tail -1 | cut -d= -f2)
  [ -z "$best" ] && best=NORESULT
  chk=$(grep -c 'full diameter check: OK' $log)
  solved=no; [ "$best" = 0 ] && solved=YES
  echo "pgl11x91 seed=$seed orbw=${W:-0} best=$best solved=$solved check_ok=$chk elapsed=${el}s" >> $SUM
  if [ "$best" = NORESULT ] && [ "$el" -lt 20 ]; then echo "ABORT: early failure, see $log" >> $SUM; exit 1; fi
  if [ "$solved" = YES ]; then
    echo "SOLVED seed=$seed file=$out" >> $SUM
    python3 /home/user/degree-diameter/research/frontier/build_haar2.py $out > $C/build_s${seed}.log 2>&1
    echo "build_haar2: $(grep -o 'VALID[A-Z_ ]*\|INVALID.*' $C/build_s${seed}.log | tail -1)" >> $SUM
    break
  fi
done
echo "done $(date +%T)" >> $SUM
