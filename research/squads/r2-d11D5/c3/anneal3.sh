#!/bin/bash
# Anneal the three best starts one after another (600 s CPU each), as specified for card c3.
cd /home/user/degree-diameter/research/squads/r2-d11D5/c3 || exit 1
for r in 0 1 2; do
  S=top/s2_r${r}.in
  [ -f "$S" ] || { echo "missing $S"; continue; }
  echo "=== start r$r: $(SCORE=1 ./plusopt5 $S)"
  SEED=1 SECS=600 T0=3 T1=0.1 PF=0.1 PH=0.7 MU=0 OUT=b${r}.in OUT0=zero${r}.in timeout 700 nice -n 19 ./plusopt5 $S > anneal_r${r}.log 2>&1
  echo "=== done r$r: $(tail -n 1 anneal_r${r}.log)"
  [ -f zero${r}.in ] && echo "ZERO FOUND r$r: zero${r}.in"
done
echo ALL_DONE
