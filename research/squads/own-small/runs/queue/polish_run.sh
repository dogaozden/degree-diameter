#!/bin/bash
# polish every state in polish_list.txt (dispatcher result lines); tables found from tasks.txt by card/k order
cd /home/user/degree-diameter/research/squads/own-small/runs/queue
T=/home/user/degree-diameter/research/squads/own-small/tools
while read k card pp NN id DD seed best n state; do
  p=${pp#p=}; N=${NN#N=}; g=${id#id=}; D=${DD#D=}; st=${state#state=}
  gf=$(grep " $p $N $g $D " tasks.txt | head -1 | awk '{print $9}')
  [ -z "$gf" ] && continue
  out=polish_${card}_$k.sol
  D=$D nice -n 5 $T/bin/polish $p $gf $g $st $out > polish_${card}_$k.log 2>&1
  echo "$card k=$k p=$p N=$N id=$g D=$D $(tail -1 polish_${card}_$k.log)" >> polish_results.txt
done < polish_list.txt
echo DONE >> polish_results.txt
