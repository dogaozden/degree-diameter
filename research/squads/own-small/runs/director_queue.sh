#!/bin/bash
cd /home/user/degree-diameter/research/squads/own-small
while ! grep -q DONE runs/scan22_D10_201_250.tsv 2>/dev/null; do sleep 10; done
nice -n 5 tools/scan22f.sh 127 160 9 runs/scan22_D9_127_160.tsv 0 93
nice -n 5 tools/scanhaar_all.sh 3 9 254 511 61 runs/haar3_D9_254_511.tsv 0
nice -n 5 tools/scanhaar_all.sh 3 10 401 700 75 runs/haar3_D10_401_700.tsv 0
nice -n 5 tools/scanhaar_all.sh 4 8 1093 1130 216 runs/haar4_D8_1093_1130.tsv 0
nice -n 5 tools/scan22f.sh 251 300 10 runs/scan22_D10_251_300.tsv 0 124
echo QUEUE-DONE > runs/director_queue.done
