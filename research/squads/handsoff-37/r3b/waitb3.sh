#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/r3b
until grep -q BATCH2_DONE out/batch2.log 2>/dev/null; do sleep 3; done
./batch3.sh > out/batch3.log 2>&1
