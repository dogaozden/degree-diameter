#!/bin/bash
# r3b batch2: symbo2 with elite restarts (STALL 400 steps without a new raw best), one heavy process at a time
cd /home/user/degree-diameter/research/squads/handsoff-37/r3b
mkdir -p out/b2
timeout 100 nice -n 10 ./symbo2 grp196_f21.txt start196_f21_far224.edges 80 5 out/b2/f196_st400 40 10 0.7 1 1000000 0.5 400 2> out/b2/f196_st400.log
echo "f196 st400 seed5: $(tail -1 out/b2/f196_st400.log) $(../bin/score37 out/b2/f196_st400_best.edges | tail -1)"
timeout 100 nice -n 10 ./symbo2 grp182_f21.txt start182_f21_far210.edges 80 6 out/b2/f182_st400 40 10 0.7 1 1000000 0.5 400 2> out/b2/f182_st400.log
echo "f182 st400 seed6: $(tail -1 out/b2/f182_st400.log) $(../bin/score37 out/b2/f182_st400_best.edges | tail -1)"
timeout 100 nice -n 10 ./symbo2 out/d5_170/grp.txt out/d5_170/start.txt 80 7 out/b2/d5_st400 40 10 0.7 1 1000000 0.5 400 2> out/b2/d5_st400.log
echo "d5_170 st400 seed7: $(tail -1 out/b2/d5_st400.log) $(../bin/score37 out/b2/d5_st400_best.edges | tail -1)"
echo BATCH2_DONE
