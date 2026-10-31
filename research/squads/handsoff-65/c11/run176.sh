#!/bin/bash
# waits for the first batch (ids 1-5), then screens the remaining order-176 groups, one at a time
C=/home/user/degree-diameter/research/squads/handsoff-65/c11
while pgrep -f "cls_screen.sh 176 5 1 2 3 4 5" >/dev/null; do sleep 5; done
cd $C && nice -n 10 ./cls_screen.sh 176 5 $(seq 6 42 | tr '\n' ' ')
echo BATCH176_DONE >> $C/cls_screen.tsv
