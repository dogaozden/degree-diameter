#!/bin/bash
# runs after the 9-flag anneal finishes (one heavy process at a time): same anneal settings on the mkdc2 KS=2 reference start e2_1 (604)
D=/home/user/degree-diameter/research/squads/r5-d11D5/c4
until grep -q "^exit " $D/anneal_9i.log; do sleep 5; done
timeout 600 nice -n 10 env SECS=400 SEED=1 T0=2 T1=0.15 PF=0.3 PH=0.7 OUT=$D/anneal_ref_e2_1_best.in /tmp/po7 /home/user/degree-diameter/research/d11D5/dc/e2_1.in > $D/anneal_ref_e2_1.log 2>&1
echo "exit $?" >> $D/anneal_ref_e2_1.log
