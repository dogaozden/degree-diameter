#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/r3b
until grep -q BATCH1_DONE out/batch1.log; do sleep 3; done
./batch2.sh > out/batch2.log 2>&1
