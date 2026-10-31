#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/r3c
export MODE=fbo BOWALK=1 STALL=1500 POOL=8 PP=60 FR=1 WCAP=16 TEN=4
for S in 401 402 403 404; do ./run.sh b1_170C5 C5 17 $S 90 >/dev/null; done
for S in 401 402; do ./run.sh b1_176C4 C4 22 $S 90 >/dev/null; done
for S in 401 402; do ./run.sh b1_176C2C2 C2xC2 22 $S 90 >/dev/null; done
for S in 401 402 403; do ./run.sh b1_180C6 C6 15 $S 90 >/dev/null; done
for S in 401 402; do ./run.sh b1_180C5 C5 18 $S 90 >/dev/null; done
for S in 401 402; do ./run.sh b1_180C3 C3 30 $S 90 >/dev/null; done
./run.sh b1_180S3 S3 15 401 90 >/dev/null
echo BATCH1_DONE >> out/runs.tsv
