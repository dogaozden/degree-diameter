#!/bin/bash
# screen.sh SECS : every (base, group) pair with diameter <= 7 bases and 802 <= bN <= 1010
cd /home/user/degree-diameter/research/squads/own-small/r1/b3
S=${1:-10}
pairs="CAT_74_0:11:1 CAT_74_0:12:1 CAT_74_0:12:2 CAT_74_0:12:3 CAT_74_0:12:4 CAT_74_0:12:5
CAT_96_1:9:1 CAT_96_1:9:2 CAT_96_1:10:1 CAT_96_1:10:2
CAT_110_0:8:1 CAT_110_0:8:2 CAT_110_0:8:3 CAT_110_0:8:4 CAT_110_0:8:5 CAT_110_0:9:1 CAT_110_0:9:2
CSS_110_0:8:1 CSS_110_0:8:2 CSS_110_0:8:3 CSS_110_0:8:4 CSS_110_0:8:5 CSS_110_0:9:1 CSS_110_0:9:2
CAT_112_0:8:1 CAT_112_0:8:2 CAT_112_0:8:3 CAT_112_0:8:4 CAT_112_0:8:5 CAT_112_0:9:1 CAT_112_0:9:2
CAT_112_1:8:1 CAT_112_1:8:2 CAT_112_1:8:3 CAT_112_1:8:4 CAT_112_1:8:5 CAT_112_1:9:1 CAT_112_1:9:2
CAT_144_0:6:1 CAT_144_0:6:2 CAT_144_0:7:1
CAT_162_0:6:1 CAT_162_0:6:2
CAT_168_0:5:1 CAT_168_0:6:1 CAT_168_0:6:2"
for p in $pairs; do
  IFS=: read b N i <<< "$p"
  ./b3lift bases/$b.txt groups/g${N}_${i}.txt $S 7 out/s_${b}_g${N}_${i} 2>&1 | tee -a out/screen.txt
done
echo DONE >> out/screen.txt
