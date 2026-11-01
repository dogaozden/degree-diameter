#!/bin/bash
# sequential pipeline (one process at a time): dump side-B candidates, search side B, search side A longer
cd /home/user/degree-diameter/research/squads/beyond-small/r2/d03
D=/home/user/degree-diameter/research/squads/beyond-small
nice -n 10 timeout 600 ./hubdump $D/data/d16D5_n33792.edges 1 15000 240 21 /dev/null candB15k > dump_B.log 2>&1
nice -n 10 timeout 600 ./mcs candB15k.cands candB15k.bits 240 3 hubsB_s3.txt 20000 10 2 > mcs_B.log 2>&1
nice -n 10 timeout 600 ./mcs candA15k.cands candA15k.bits 240 5 hubsA_s5.txt 20000 10 2 > mcs_A5.log 2>&1
echo DONE > run_all.done
