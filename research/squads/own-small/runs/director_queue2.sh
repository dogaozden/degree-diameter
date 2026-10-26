#!/bin/bash
cd /home/user/degree-diameter/research/squads/own-small
nice -n 12 tools/scan_bicoset.sh 10 802 1000 runs/bicoset_D10_802_1000.tsv
nice -n 12 tools/scan_bicoset.sh 9 508 700 runs/bicoset_D9_508_700.tsv
nice -n 12 tools/scan_bicoset.sh 8 290 400 runs/bicoset_D8_290_400.tsv
nice -n 12 tools/scan_bicoset.sh 7 194 254 runs/bicoset_D7_194_254.tsv
echo QUEUE2-DONE > runs/director_queue2.done
