#!/bin/bash
# Stage 1: small orders (116,117,118) x 17 bases; Stage 2: order 120 non-abelian x 17 bases.
T=/home/user/degree-diameter/research/s65/tools
G=/home/user/degree-diameter/research/s65/groups/sg
C=/home/user/degree-diameter/research/squads/s65r1/c3
cd $C
OUT=screen.txt
: > $OUT
run() { # group_file base_file iters secs seed tag
  local g=$1 b=$2 it=$3 secs=$4 seed=$5 tag=$6
  local bn=$(basename $b .txt); local gn=$(basename $g .txt)
  local sol=runs/${tag}_${gn}_${bn}_s${seed}.sol
  local res=$(D=5 SECS=$secs ITERS=$it SEED=$seed OUT=$sol timeout 60 nice -n 10 $T/vl $b $g 2>/dev/null | grep '^RESULT best')
  local cost=$(echo "$res" | awk '{print $3}')
  echo "$gn $bn cost=$cost seed=$seed iters=$it secs=$secs sol=$sol" >> $OUT
}
for g in sg_116_1 sg_116_3 sg_116_4 sg_117_1 sg_117_3 sg_118_1; do
  for b in bases/m*.txt; do run $G/$g.txt $C/$b 30000 4 1 st1; done
done
echo STAGE1_DONE >> $OUT
for gf in $G/sg_120_*.txt; do
  gn=$(basename $gf .txt)
  case $gn in sg_120_4|sg_120_31|sg_120_47) continue;; esac
  for b in bases/m*.txt; do run $gf $C/$b 12000 1.5 1 st2; done
done
echo STAGE2_DONE >> $OUT
