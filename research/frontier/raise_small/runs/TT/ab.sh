#!/bin/bash
# A/B: targeted moves (TARGP=40) vs plain (TARGP=0), 60 CPU-s each, D=13, 2+2 over Z93 x|_5 Z12 (N=1116; plain scan reached 18)
cd /home/user/degree-diameter/research/frontier/raise_small
python3 tools/gtab.py runs/TT/g1116.tab 93 12 5 2>/dev/null
for s in 1 2; do for tp in 0 40; do
  echo "seed $s TARGP $tp: $(D=13 TARGP=$tp timeout 900 bin/saliftt 2 runs/TT/g1116.tab 1 $s 60 10 0.3 runs/TT/ab_${tp}_$s.sol | tail -1)" >> runs/TT/ab.out
done; done
