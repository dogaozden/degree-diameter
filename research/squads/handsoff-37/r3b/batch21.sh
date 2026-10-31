#!/bin/bash
# r3b batch21 (coordinator redirect): fresh SAT starts on the D5 sigma 2^7 1^3 group (n = 170), symbo PV 0.5, K 80, 90 s each, seeds 61..68
cd /home/user/degree-diameter/research/squads/handsoff-37/r3b
G=out/b16/d5_170_2to7/grp.txt
for seed in 61 62 63 64 65 66 67 68; do
  mkdir -p out/b21/fs$seed
  python3 mkgroup.py 5 17 4 "2,2,2,2,2,2,2,1,1,1" "2,2,2,2,2,2,2,1,1,1" out/b21/fs$seed/grp.txt out/b21/fs$seed/start.txt $seed > out/b21/fs$seed/mk.log 2>&1 || { echo "mk fail $seed"; continue; }
  timeout 100 nice -n 10 ./symbo out/b21/fs$seed/grp.txt out/b21/fs$seed/start.txt 90 $seed out/b21/fs$seed/best 80 10 0.7 1 1000000 0.5 2> out/b21/fs$seed/s.log || true
  echo "fresh seed=$seed PV=0.5 K=80: $(tail -1 out/b21/fs$seed/s.log) $(../bin/score37 out/b21/fs$seed/best_best.edges | tail -1)"
done
echo BATCH21_DONE
