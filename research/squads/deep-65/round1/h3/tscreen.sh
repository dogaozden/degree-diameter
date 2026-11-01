#!/bin/bash
# usage: tscreen.sh ORDER TLIM SEED "grp list" "a list" : tabu3 (exact bad objective), one line per run
ORD=$1; TL=$2; SD=$3; GL=$4; AL=$5
cd /home/user/degree-diameter/research/squads/deep-65/round1/h3
for g in $GL; do for a in $AL; do
  timeout 100 nice -n 10 ./bin/tabu3 groups/sg_${ORD}_${g}.txt $a $SD 100000000 4 $TL edges/ts_${ORD}_${g}_a${a}_s${SD}.edges > logs/ts_${ORD}_${g}_a${a}_s${SD}.txt 2>&1
  r=$(grep RESULT logs/ts_${ORD}_${g}_a${a}_s${SD}.txt | awk '{print $3}')
  st=$(grep RESULT logs/ts_${ORD}_${g}_a${a}_s${SD}.txt | awk '{print $5}')
  echo "ORD $ORD grp $g a $a seed $SD cost2bad $r bad $((r/2)) steps $st"
done; done
