#!/bin/bash
# cmp_tools.sh: after screen1 finishes, compare wt12 (uniform random moves) and wtt (far-target moves), 60 s each
W=/home/user/degree-diameter/research/squads/handsoff-49/w12
cd $W
while [ "$(wc -l < screen1.tsv)" -lt 78 ]; do sleep 15; done
nice -n 10 timeout 120 ./wt12 bases/b4_mh2_1.txt groups/pgl11.bin 9 60 3 runs/cmp_wt12 100 20 > logs/cmp_wt12.out 2> logs/cmp_wt12.err
nice -n 10 timeout 120 ./wtt bases/b4_mh2_1.txt groups/pgl11.bin 9 60 3 runs/cmp_wtt 10 20 100 10 20 > logs/cmp_wtt.out 2> logs/cmp_wtt.err
echo "wt12: $(tail -1 logs/cmp_wt12.out)"
echo "wtt : $(tail -1 logs/cmp_wtt.out)"
