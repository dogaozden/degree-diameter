#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/r3b
while kill -0 15801 2>/dev/null; do sleep 2; done
./batch13.sh > out/batch13.log 2>&1
