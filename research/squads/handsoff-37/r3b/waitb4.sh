#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/r3b
until grep -q BATCH3_DONE out/batch3.log 2>/dev/null; do sleep 3; done
./batch4.sh > out/batch4.log 2>&1
