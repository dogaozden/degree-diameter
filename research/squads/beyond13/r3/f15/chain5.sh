#!/bin/bash
# chain hmeta runs on one (5,11) group, each link continues from the best saved S with a new seed
B=/home/user/degree-diameter/research/frontier/beyond13
cd /home/user/degree-diameter/research/squads/beyond13/r3/f15
m=$1; k=$2; r=$3; S=$4; links=$5; tag=$6
for i in $(seq 1 $links); do
  seed=$((100+i))
  if [ -f ch_${tag}.best ]; then st=ch_${tag}.best; else st=""; fi
  if [ -n "$st" ]; then
    res=$(START=$st THREADS=1 nice -n 10 timeout 200 $B/meta/hmeta 5 11 $S $seed 8 ch_${tag} $m $k $r 2>&1 | grep RESULT)
  else
    res=$(THREADS=1 nice -n 10 timeout 200 $B/meta/hmeta 5 11 $S $seed 8 ch_${tag} $m $k $r 2>&1 | grep RESULT)
  fi
  echo "link $i seed $seed :: $res" >> chain_${tag}.log
  if [ -f ch_${tag} ]; then echo FOUND >> chain_${tag}.log; break; fi
done
echo DONE >> chain_${tag}.log
