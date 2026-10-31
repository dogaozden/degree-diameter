#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/r3c
while ! grep -q BATCH2_DONE out/runs.tsv; do sleep 10; done
export MODE=fbo BOWALK=1 STALL=1500 POOL=8 PP=60 FR=1 WCAP=16 TEN=4
./run.sh b3_168S3 S3 14 1 90 >/dev/null
for S in 402 403; do ./run.sh b3_180S3 S3 15 $S 90 >/dev/null; done
./run.sh b3_192S3 S3 16 1 90 >/dev/null
echo BATCH3_DONE >> out/runs.tsv
