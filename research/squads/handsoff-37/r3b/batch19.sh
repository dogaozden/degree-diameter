#!/bin/bash
# r3b batch19 (coordinator redirect): breakout symbo on D5 = Z5 x| Z2 (alpha 4, sigma 2^7 1^3 both sides), n = 170.
# (a) from r3a's far-60 graph (G-invariant under this group file), PV 0.8 and PV 0.5; (b) fresh SAT starts, seeds 53..60; 90 s each.
cd /home/user/degree-diameter/research/squads/handsoff-37/r3b
G=out/b16/d5_170_2to7/grp.txt
timeout 100 nice -n 10 ./symbo $G out/b19/r3a_far60_start.edges 90 51 out/b19/r3a60_pv08 40 10 0.7 1 1000000 0.8 2> out/b19/r3a60_pv08.log
echo "r3a60 start PV=0.8 seed=51: $(tail -1 out/b19/r3a60_pv08.log) $(../bin/score37 out/b19/r3a60_pv08_best.edges | tail -1)"
timeout 100 nice -n 10 ./symbo $G out/b19/r3a_far60_start.edges 90 52 out/b19/r3a60_pv05 40 10 0.7 1 1000000 0.5 2> out/b19/r3a60_pv05.log
echo "r3a60 start PV=0.5 seed=52: $(tail -1 out/b19/r3a60_pv05.log) $(../bin/score37 out/b19/r3a60_pv05_best.edges | tail -1)"
for seed in 53 54 55 56 57 58 59 60; do
  mkdir -p out/b19/fs$seed
  python3 mkgroup.py 5 17 4 "2,2,2,2,2,2,2,1,1,1" "2,2,2,2,2,2,2,1,1,1" out/b19/fs$seed/grp.txt out/b19/fs$seed/start.txt $seed > out/b19/fs$seed/mk.log 2>&1 || { echo "mk fail $seed"; continue; }
  timeout 100 nice -n 10 ./symbo out/b19/fs$seed/grp.txt out/b19/fs$seed/start.txt 90 $seed out/b19/fs$seed/best 40 10 0.7 1 1000000 0.8 2> out/b19/fs$seed/s.log
  echo "fresh seed=$seed PV=0.8: $(tail -1 out/b19/fs$seed/s.log) $(../bin/score37 out/b19/fs$seed/best_best.edges | tail -1)"
done
echo BATCH19_DONE
