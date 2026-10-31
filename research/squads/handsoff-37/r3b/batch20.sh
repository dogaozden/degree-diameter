#!/bin/bash
# r3b batch20 (coordinator redirect follow-up): variants from r3a's far-60 graph on the D5 sigma 2^7 1^3 group, 90 s each:
# K = 200 candidates per step (PV 0.8); PV 0.95 (almost only voltage moves); symbo2 with elite restarts (STALL 300), PV 0.8
cd /home/user/degree-diameter/research/squads/handsoff-37/r3b
G=out/b16/d5_170_2to7/grp.txt
S=out/b19/r3a_far60_start.edges
timeout 100 nice -n 10 ./symbo $G $S 90 61 out/b20/k200 200 10 0.7 1 1000000 0.8 2> out/b20/k200.log || true
echo "r3a60 K=200 PV=0.8 seed=61: $(tail -1 out/b20/k200.log) $(../bin/score37 out/b20/k200_best.edges | tail -1)"
timeout 100 nice -n 10 ./symbo $G $S 90 62 out/b20/pv95 40 10 0.7 1 1000000 0.95 2> out/b20/pv95.log || true
echo "r3a60 PV=0.95 seed=62: $(tail -1 out/b20/pv95.log) $(../bin/score37 out/b20/pv95_best.edges | tail -1)"
timeout 100 nice -n 10 ./symbo2 $G $S 90 63 out/b20/st300 40 10 0.7 1 1000000 0.8 300 2> out/b20/st300.log || true
echo "r3a60 STALL=300 PV=0.8 seed=63: $(tail -1 out/b20/st300.log) $(../bin/score37 out/b20/st300_best.edges | tail -1)"
echo BATCH20_DONE
