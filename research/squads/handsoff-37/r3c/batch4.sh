#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/r3c
while ! grep -q BATCH3_DONE out/runs.tsv; do sleep 10; done
export MODE=fbo BOWALK=1 STALL=1500 POOL=8 PP=60 FR=1 WCAP=16 TEN=4
for S in 404 405 406 407; do ./run.sh b4_180S3 S3 15 $S 90 >/dev/null; done
for S in 404 405; do ./run.sh b4_180C6 C6 15 $S 90 >/dev/null; done
echo BATCH4_DONE >> out/runs.tsv
