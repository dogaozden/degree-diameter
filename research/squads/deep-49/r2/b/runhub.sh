#!/bin/bash
# usage: runhub.sh NAME CPU SEED  (table NAME.tab in this folder); appends a summary line to results.txt
cd /home/user/degree-diameter/research/squads/deep-49/r2/b
name=$1; cpu=$2; seed=$3
nice -n 10 timeout 100 ./hubs ./$name.tab $cpu $seed 9 runs/hub_${name}_s${seed}.edges > runs/hub_${name}_s${seed}.log 2>&1
echo "hub $name seed $seed cpu $cpu: $(grep -E 'FINAL|subgroups' runs/hub_${name}_s${seed}.log | tr '\n' ' ')" >> results.txt
tail -1 results.txt
