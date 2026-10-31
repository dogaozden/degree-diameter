#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/r3b
until grep -q BATCH7_DONE out/batch7.log 2>/dev/null; do sleep 3; done
./batch8.sh > out/batch8.log 2>&1
