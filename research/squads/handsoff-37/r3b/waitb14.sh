#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/r3b
until grep -q BATCH13_DONE out/batch13.log 2>/dev/null; do sleep 3; done
./batch14.sh > out/batch14.log 2>&1
