#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/r3b
until grep -q BATCH16_DONE out/batch16.log 2>/dev/null; do sleep 3; done
./batch17.sh > out/batch17.log 2>&1
