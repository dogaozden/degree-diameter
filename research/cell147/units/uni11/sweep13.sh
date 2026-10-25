#!/bin/bash
# sweep all similitudes T of A (multiplier -nu) x {L,R} at prime q; short orbitclique runs
q=$1; C=$2; secs=$3; n=$4
cd /home/user/degree-diameter/research/cell147/units/uni11
for t in $(seq 0 $((n-1))); do for m in L R; do echo "$t $m"; done; done | xargs -P 2 -n 2 sh -c '
  python3 permq2.py '$q' '$C' $1 $0 jperms/s'$q'_$1_$0.txt > /dev/null
  Q='$q' nice -n 5 timeout 300 ./orbitclique_q ../../data/E'$q'.map jperms/s'$q'_$1_$0.txt '$secs' 1 flags/s'$q'_$1_$0.flags 2> logs/s'$q'_$1_$0.log > /dev/null
  echo "t=$0 $1: $(grep -o "[0-9]* orbits ([0-9]* usable); sizes:.*" logs/s'$q'_$1_$0.log | cut -c1-80) | $(grep -o "best: .*points" logs/s'$q'_$1_$0.log)"'
