#!/bin/bash
# r3b batch4: symbo3 (raw margin restart) on F20 170 and D5 170, and F21 182 from the far-210 start
cd /home/user/degree-diameter/research/squads/handsoff-37/r3b
mkdir -p out/b4
timeout 100 nice -n 10 ./symbo3 out/f20_170/grp.txt out/f20_170/start.txt 80 11 out/b4/f20_m30 40 10 0.7 1 1000000 0.5 0 30 2> out/b4/f20_m30.log
echo "f20 170 marg30 seed11: $(tail -1 out/b4/f20_m30.log) $(../bin/score37 out/b4/f20_m30_best.edges | tail -1)"
timeout 100 nice -n 10 ./symbo3 out/f20_170/grp.txt out/f20_170/start.txt 80 12 out/b4/f20_m10 80 10 0.5 1 4 0.5 0 10 2> out/b4/f20_m10.log
echo "f20 170 K80 PF0.5 WCAP4 marg10 seed12: $(tail -1 out/b4/f20_m10.log) $(../bin/score37 out/b4/f20_m10_best.edges | tail -1)"
timeout 100 nice -n 10 ./symbo3 grp182_f21.txt start182_f21_far210.edges 80 13 out/b4/f182_m20 40 10 0.7 1 1000000 0.5 0 20 2> out/b4/f182_m20.log
echo "f182 marg20 seed13: $(tail -1 out/b4/f182_m20.log) $(../bin/score37 out/b4/f182_m20_best.edges | tail -1)"
echo BATCH4_DONE
