#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/r3b
until grep -q BATCH12_DONE out/batch12.log 2>/dev/null; do sleep 3; done
./batch13.sh > out/batch13.log 2>&1
