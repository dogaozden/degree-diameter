#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/r3b
until grep -q BATCH11_DONE out/batch11.log 2>/dev/null; do sleep 3; done
./batch12.sh > out/batch12.log 2>&1
