#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/r3c
export MODE=fbo BOWALK=1 STALL=1500 POOL=8 PP=60 FR=1 WCAP=16 TEN=4
for S in 414 415 416 417 418; do ./run.sh b7_180S3 S3 15 $S 90 >/dev/null; done
echo BATCH7_DONE >> out/runs.tsv
