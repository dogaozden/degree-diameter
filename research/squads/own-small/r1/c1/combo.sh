#!/bin/bash
C=/home/user/degree-diameter/research/squads/own-small/r1/c1
cd $C/groups
for N in 134 135 138 140 142 146 147 148 150 152 154 155 156 158 164 165 166 170; do python3 /home/user/degree-diameter/research/squads/own-small/tools/split_groups.py t$N.txt . ; done
for f in g*.info; do grep -q "abelian=0" $f && echo ${f%.info}.bin; done > $C/nonab.list
wc -l < $C/nonab.list
rm -f $C/scr/screen.tsv
/home/user/degree-diameter/research/squads/own-small/r1/c1/screen.sh $C/nonab.list 1.2
echo COMBO_DONE
