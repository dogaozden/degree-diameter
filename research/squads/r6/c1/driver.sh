#!/bin/bash
# Card r6 c1: (8,8) at N = 120,120, group sl 11 91, ORBIT "3 2 2".
# Seeds 41..56, 90 s each (timeout 190). Odd seeds plain, even seeds ORBW=3. Stop at first best=0.
B=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin
D=/home/user/degree-diameter/research/squads/r6/c1
BUILD=/home/user/degree-diameter/research/frontier/build_haar2.py
S=$D/summary.txt
cd "$D" || exit 1
unset ORBW

SOLVED=0
echo "start $(date +%T)" >> "$S"
for seed in $(seq 41 56); do
  w=0
  if [ $((seed % 2)) -eq 0 ]; then w=3; fi
  suffix=""
  if [ "$w" != 0 ]; then suffix="_w$w"; fi
  base=$D/sl11_91${suffix}_s${seed}
  t0=$(date +%T)
  if [ "$w" != 0 ]; then
    ORBIT="3 2 2" ORBW=$w timeout 190 nice -n 10 "$B/haar_sym" 8 8 90 "$seed" 8 "$base.txt" sl 11 91 > "$base.log" 2>&1
  else
    ORBIT="3 2 2" timeout 190 nice -n 10 "$B/haar_sym" 8 8 90 "$seed" 8 "$base.txt" sl 11 91 > "$base.log" 2>&1
  fi
  rc=$?
  best=$(grep -E 'RESULT.*best=' "$base.log" | grep -oE 'best=[0-9]+' | tail -1 | cut -d= -f2)
  ver=""
  if [ "$best" = "0" ] && [ -s "$base.txt" ]; then
    ver=$(python3 "$BUILD" "$base.txt" 2>&1 | tail -1)
    SOLVED=1
  fi
  echo "sl11_91${suffix} | ORBIT=3 2 2 | seed=$seed | ORBW=$w | start=$t0 | rc=$rc | best=${best:-NA} | $ver" >> "$S"
  if [ "$SOLVED" = 1 ]; then break; fi
done
echo "end $(date +%T) solved=$SOLVED" >> "$S"
