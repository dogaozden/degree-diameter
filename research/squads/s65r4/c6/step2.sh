#!/bin/bash
# step2_in.txt lines: FILE "S" "R" "L" ; runs tabu with seeds 1 and 2 on the 2+2 lift of each bi-Cayley graph.
cd /home/user/degree-diameter/research/squads/s65r4/c6
TOOLS=/home/user/degree-diameter/research/s65/tools
BC=/home/user/degree-diameter/research/s65/groups/bc
k=0
while read f S R L; do
  k=$((k+1)); n=g$k
  python3 $TOOLS/bicay2lift.py $BC/$f "$S" "$R" "$L" $n.base E_$n.txt > $n.conv.log 2>&1 || { echo "CONV FAIL $f" >> step2.tsv; continue; }
  python3 $TOOLS/normlift.py $n.base E_$n.txt bn_$n.base || { echo "NORM FAIL $f" >> step2.tsv; continue; }
  for s in 1 2; do
    SECS=75 SEED=$s timeout 150 nice -n 10 $TOOLS/tabu bn_$n.base E_$n.txt out_${n}_s$s.sol > tabu_${n}_s$s.log 2> tabu_${n}_s$s.err
    r=$(grep '^RESULT' tabu_${n}_s$s.log | head -1)
    printf "%s\t%s\tseed%s\t%s\t%s\n" "$n" "$f" "$s" "$S|$R|$L" "$r" >> step2.tsv
  done
done < step2_in.txt
echo DONE >> step2.tsv
