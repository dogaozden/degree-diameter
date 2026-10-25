#!/bin/bash
# c1 pipeline (Haiku squad round 3, card c1): quotient annealing (6 seeds x 40 s per graph) -> expand best -> ktabu polish 420 s.
C=/home/user/degree-diameter/research/squads/d16D7_r3/c1
R=/home/user/degree-diameter/research/squads/d16D7_r3
R2=/home/user/degree-diameter/research/squads/d16D7_r2
S=$R/run_slot.sh
EXP=/home/user/degree-diameter/research/squads/cells/d16D7/ogquot_expand.py
cd $C
# phase 1: quotient search
for g in pts lines; do
  for seed in 1 2 3 4 5 6; do
    if [ $seed -le 3 ]; then P="4 0.15 2000000"; else P="2.5 0.3 5000000"; fi
    $S $C/wsa $R/quot/q9_$g.txt $C/runs/q_${g}_s$seed.sol 40 $seed $P > $C/runs/q_${g}_s$seed.log 2>&1
  done
done
echo phase1_done
# phase 2: pick best quotient solution per graph, expand, score
for g in pts lines; do
  best=""; bw=-1
  for seed in 1 2 3 4 5 6; do
    f=$C/runs/q_${g}_s$seed.sol
    [ -s $f ] || continue
    line=$(python3 $C/qeval.py $R/quot/q9_$g.txt $f)
    w=$(echo "$line" | sed -n 's/^weight \([0-9]*\) .*independent True.*/\1/p')
    if [ -n "$w" ] && [ "$w" -gt "$bw" ]; then bw=$w; best=$f; fi
  done
  cp $best $C/runs/bestq_$g.sol
  python3 $EXP $R/quot/q9_$g.map $C/runs/bestq_$g.sol $C/runs/exp_$g.txt
  if [ $g = pts ]; then OG=$R2/og_pts.txt; else OG=$R2/og_lines.txt; fi
  python3 $R2/ogscore.py $OG $C/runs/exp_$g.txt | tee $C/runs/exp_${g}.score
done
echo phase2_done
# phase 3: polish expansions with ktabu on the full orbit graph (420 s each)
for g in pts lines; do
  if [ $g = pts ]; then OG=$R2/og_pts.txt; else OG=$R2/og_lines.txt; fi
  $S $R2/c2/ktabu $OG $C/runs/exp_$g.txt $C/runs/pol_$g.sol 420 $([ $g = pts ] && echo 11 || echo 12) > $C/runs/pol_$g.log 2>&1
  echo polish_${g}_rc=$?
done
echo DONE
