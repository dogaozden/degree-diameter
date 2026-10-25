#!/bin/sh
# q = 9, C_91 (Singer power) equivariant lifts with random voltages (eqlift.py seed 1, holonomy on, hops at distance 5);
# exact unreached count at D = 8 for M = 16, 18, 20, 22.  Output: eq/q9_frontier_out.txt
cd "$(dirname "$0")/.." || exit 1
T=${TMPDIR:-/tmp}
for M in 16 18 20 22; do
  python3 eqlift.py 9 91 $M 1 $T/eq9_$M.txt 1 5 singer
  echo "M $M: $(./liftdiam $T/eq9_$M.txt 8 2 | tr '\n' ' ')"
done
