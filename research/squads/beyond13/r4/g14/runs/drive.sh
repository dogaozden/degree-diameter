#!/bin/bash
# g14 driver: round-robin chained hmeta links over three single Frobenius groups with N >= 1,763,000 at (5,13)
B=/home/user/degree-diameter/research/frontier/beyond13
C=/home/user/degree-diameter/research/squads/beyond13/r4/g14/runs
GRP=("135617 13 15086" "47657 37 34427" "41023 43 35942")
K=8
for link in 1 2 3 4; do
  for gi in 0 1 2; do
    set -- ${GRP[$gi]}; m=$1; k=$2; r=$3
    tag=g$gi
    out=$C/$tag
    seed=$((100*link + gi + 7))
    if [ -f $out.best ]; then
      THREADS=1 START=$out.best timeout 105 nice -n 10 $B/meta/hmeta 5 13 95 $seed $K $out.new $m $k $r > $C/$tag.link$link.log 2>&1
      if [ -f $out.new.best ]; then mv $out.new.best $out.best; fi
    else
      THREADS=1 timeout 105 nice -n 10 $B/meta/hmeta 5 13 95 $seed $K $out $m $k $r > $C/$tag.link$link.log 2>&1
      if [ -f $out.best ]; then :; fi
    fi
    echo "link $link $tag $(grep RESULT $C/$tag.link$link.log)" >> $C/driver.log
    if [ -f $out.new ]; then echo "SOLVED $tag" >> $C/driver.log; fi
  done
done
echo DONE >> $C/driver.log
