#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/r3b
until grep -q BATCH19_DONE out/batch19.log 2>/dev/null; do sleep 3; done
./batch20.sh > out/batch20.log 2>&1
