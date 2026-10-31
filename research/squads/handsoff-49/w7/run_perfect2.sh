#!/bin/bash
# perfect or near-perfect candidates: PGL(2,19) (n = 6840, H involution), A5 x PSL(2,7) (n = 6720 with H of order 3)
cd /home/user/degree-diameter/research/squads/handsoff-49/w7
LOG=$PWD/results_perfect2.tsv
: > $LOG
nice -n 10 python3 build_tabs.py PGL2_19 >> build_p2.log 2>&1 && nice -n 10 python3 batch.py $LOG 20 300000 tabs/PGL2_19.bin >> batch_p2_stdout.log 2>&1
nice -n 10 python3 build_perm_prod.py "A5*PSL2_7" >> build_p2.log 2>&1 && nice -n 10 python3 batch.py $LOG 20 300000 tabs/A5xPSL2_7.bin >> batch_p2_stdout.log 2>&1
echo ALLDONE >> $LOG
