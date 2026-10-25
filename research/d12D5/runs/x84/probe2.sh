#!/bin/bash
cd /home/user/degree-diameter/research/d12D5
for job in "runs/x84/dic7.txt 2" "tables/z28.txt 6" "runs/x84/d14.txt 2" "tables/z29.txt 3" "tables/z28.txt 7"; do
  set -- $job; echo "$1 seed $2 $(FAKE=1 DIAGBT=1 timeout 400 nice ./mlift_ejoint2 base_k33m.txt $1 90 $2 2 1.0 | tail -1 | grep -o 'm=[0-9]* best_cost=[0-9]*')"
done
