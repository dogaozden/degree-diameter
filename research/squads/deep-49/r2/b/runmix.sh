#!/bin/bash
# usage: runmix.sh NAME CPU SEED  (table NAME.tab in this folder); appends a summary line to results.txt
cd /home/user/degree-diameter/research/squads/deep-49/r2/b
name=$1; cpu=$2; seed=$3
nice -n 10 timeout 100 ./mixed ./$name.tab $cpu $seed 9 runs/${name}_s${seed}.edges > runs/${name}_s${seed}.log 2>&1
echo "mix $name seed $seed cpu $cpu: $(tail -1 runs/${name}_s${seed}.log)" >> results.txt
tail -1 results.txt
