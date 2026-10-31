#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/r3b
until grep -q BATCH15_DONE out/batch15.log 2>/dev/null; do sleep 3; done
./batch16.sh > out/batch16.log 2>&1
