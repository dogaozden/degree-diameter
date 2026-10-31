#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/r3b
until grep -q BATCH16_DONE out/batch16.log 2>/dev/null; do sleep 3; done
./batch18.sh > out/batch18.log 2>&1
