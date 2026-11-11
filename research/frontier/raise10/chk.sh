#!/bin/bash
# chk.sh SOL [THREADS]: independent low-memory check (hcheckpsl for psl, hcheck5 for sl) of a haar_big0 solution;
# log in checks/<stem>.<checker>.txt; a VALID solution is copied to sols/ and ../sols/.
cd "$(dirname "$0")"; f=$1; th=${2:-2}; stem=$(basename $f .out); stem=${stem%.txt}
fam=$(head -1 $f | awk '{print $3}'); if [ "$fam" = psl ]; then c=hcheckpsl; else c=hcheck5; fi
OMP_NUM_THREADS=$th THREADS=$th ./check_one.sh $c checks/$stem.$c.txt ./bin/$c $f
v=$(grep -h -E "^VALID|^INVALID" checks/$stem.$c.txt | tail -1); echo "$v"
if echo "$v" | grep -q "^VALID"; then cp $f sols/$stem.txt; cp $f ../sols/$stem.txt; echo "saved sols/$stem.txt"; fi
