#!/bin/bash
# calibration of the fixed-vertex (hub) Z3 model: m = 3k + 1
cd /home/user/degree-diameter/research/squads/handsoff-37/r2c
nice -n 10 ./lift2 27 3 1 21 240 1.5 0.2 2000000 out/h82 | grep -E "new best|FINAL|ZERO" | tail -4
