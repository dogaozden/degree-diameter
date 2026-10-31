#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/r3b
until grep -q BATCH8_DONE out/batch8.log 2>/dev/null; do sleep 3; done
./batch9.sh > out/batch9.log 2>&1
