#!/bin/bash
cd /home/user/degree-diameter/research/frontier/raise_small
python3 tools/gtab.py runs/TT/g1100.tab 55 20 2 2>/dev/null
for s in 11 12 13; do for tp in 0 40; do
  echo "seed $s TARGP $tp: $(D=13 TARGP=$tp timeout 900 bin/saliftt 2 runs/TT/g1100.tab 1 $s 40 10 0.3 runs/TT/ab2_${tp}_$s.sol | tail -1)" >> runs/TT/ab2.out
done; done
