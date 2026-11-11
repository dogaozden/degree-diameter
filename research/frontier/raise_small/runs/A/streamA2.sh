#!/bin/bash
# director stream A: D=14 chains on the two cost-2 states, alternating, 100 CPU-s links
cd /home/user/degree-diameter/research/frontier/raise_small
for round in 1 2 3 4; do
  tools/chain.sh 14 4 29 28 2 runs/probe14/o4/g812_29_28_2_D14_p4_s1.sol.best 100 2 $((1000+100*round)) runs/A/c812
  grep -q VALID runs/A/c812/chain.log && break
  tools/chain.sh 14 4 17 48 3 runs/probe14/o2/g816_17_48_3_D14_p4_s1.sol.best 100 2 $((1050+100*round)) runs/A/c816
  grep -q VALID runs/A/c816/chain.log && break
done
