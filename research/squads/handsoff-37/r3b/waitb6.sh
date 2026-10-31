#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/r3b
until grep -q BATCH5_DONE out/batch5.log 2>/dev/null; do sleep 3; done
./batch6.sh > out/batch6.log 2>&1
