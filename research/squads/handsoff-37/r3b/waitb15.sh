#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/r3b
until grep -q BATCH14_DONE out/batch14.log 2>/dev/null; do sleep 3; done
./batch15.sh > out/batch15.log 2>&1
