#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/r3b
until grep -q BATCH10_DONE out/batch10.log 2>/dev/null; do sleep 3; done
./batch11.sh > out/batch11.log 2>&1
