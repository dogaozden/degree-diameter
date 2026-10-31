#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/r3b
until grep -q BATCH4_DONE out/batch4.log 2>/dev/null; do sleep 3; done
./batch5.sh > out/batch5.log 2>&1
