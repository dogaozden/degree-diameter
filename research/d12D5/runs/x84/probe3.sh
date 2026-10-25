#!/bin/bash
cd /home/user/degree-diameter/research/d12D5
for job in "base_k2_2.txt tables/z41.txt" "base_k2_1.txt tables/z41.txt" "base_k2_3.txt tables/z41.txt" "base_k2_2.txt tables/z42.txt"; do
  set -- $job; echo "$1 $2 $(FAKE=1 DIAGBT=1 timeout 400 nice ./mlift_ejoint2 $1 $2 90 1 2 1.0 | tail -1 | grep -o 'm=[0-9]* best_cost=[0-9]*')"
done
