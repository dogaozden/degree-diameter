#!/bin/bash
# usage: score.sh TAG P0FILE P1FILE S3FILE S4FILE   (files relative to c5/); writes work_TAG and score_TAG.log
cd /home/user/degree-diameter/research/squads/c157b-r2/c5 || exit 1
S=/home/user/degree-diameter/research/squads/c157b-r2/shared
timeout 1200 nice -n 10 python3 /home/user/degree-diameter/research/d15D7b/score_relaxed.py $S/hex_q11.bin $S/d14D7_hex11_mirror768_n1774632.sol $S "$2" "$3" "$4" "$5" work_$1 > score_$1.log 2>&1
echo "[$1] $(grep -E '^SCORE|^dropped' score_$1.log | tr '\n' ' ')"
