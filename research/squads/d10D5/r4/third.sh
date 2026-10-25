#!/bin/bash
# third.sh "X1 X2 ..." SEED: coverage(+D1) stage for third-flag candidates {1,6,X} from the 4,840 state (sequential, 1 core)
for X in $1; do
  python3 mkhubF.py ../hubs/graphs/d10D5_n4840_flagdel2.sol "1 6 $X" runs/k40_$X.sol $2 | tail -n 1
  ./fdrun.sh runs/k40_$X.sol "1 6 $X" runs/f40_${X}s$2 $2 300 0.2 | sed "s/^/X=$X /"
done
