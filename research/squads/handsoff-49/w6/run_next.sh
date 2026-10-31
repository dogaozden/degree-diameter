#!/bin/bash
# w6: after the Haar group runs: surgery annealing in mode 3 (3 removed edges + edge ab), 240 s, two seeds.
H=/home/user/degree-diameter/research/squads/handsoff-49
cd $H/w6
while ! grep -q DONE groups/summary.txt 2>/dev/null; do sleep 2; done
for seed in 21 22; do
  timeout 400 nice -n 10 ./surgsa2 ../seeds/valid4970.edges tmp/surgsa3_$seed.edges 240 $seed 3 6 0.5 2> tmp/surgsa3_$seed.log > tmp/surgsa3_$seed.out
  echo "mode3 seed $seed: $(cat tmp/surgsa3_$seed.out)" >> groups/summary.txt
done
echo NEXTDONE >> groups/summary.txt
