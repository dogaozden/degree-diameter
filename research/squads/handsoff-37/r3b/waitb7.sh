#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/r3b
until grep -q BATCH6_DONE out/batch6.log 2>/dev/null; do sleep 3; done
./batch7.sh > out/batch7.log 2>&1
