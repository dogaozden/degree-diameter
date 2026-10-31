#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/r3c
while ! grep -q BATCH4_DONE out/runs.tsv; do sleep 10; done
export MODE=fbo BOWALK=1 STALL=1500 POOL=8 PP=60 FR=1 WCAP=16 TEN=4
for S in 408 409 410 411; do ./run.sh b5_180S3 S3 15 $S 90 >/dev/null; done
echo BATCH5_DONE >> out/runs.tsv
