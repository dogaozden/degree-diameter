#!/bin/bash
# (4,8): Haar graphs of every group of the 11 orders in 1093..1130 that the first scan could not read (their library data
# was installed later, package gap-smallgrp-extra); order 1120 (1,092 groups) is left out for time.
cd /home/user/degree-diameter/research/squads/own-small
for N in 1096 1098 1100 1104 1107 1110 1112 1116 1122 1125 1128; do
  GDIR=/tmp/claude-0/-home-user-degree-diameter/6bbfb942-4016-5a09-834c-7684c0cc81b5/scratchpad/groups/h48m nice -n 5 tools/scanhaar_all.sh 4 8 $N $N 216 runs/haar4_D8_missing.tsv 0
done
echo ALLDONE >> runs/haar4_D8_missing.tsv
