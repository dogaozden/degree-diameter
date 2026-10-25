#!/bin/bash
# exact.sh Q HEX PHI SPEC... : design at q=Q (hexmode HEX, phimode PHI, seed 7), exact cost over all A-sources
Q=$1; HX=$2; PH=$3; shift 3
for g in "$@"; do
  tag=s${Q}_${g}_${HX}_${PH}
  python3 mk_nl.py $Q $g ${SEED:-7} $HX $PH scan/$tag > /dev/null 2>&1 || { echo "$g: mk failed"; continue; }
  out=$(timeout 900 nice -n 10 ./nlift scan/$tag.grp scan/$tag.base 8 all 2>/dev/null)
  echo "q$Q $g hex=$HX phi=$PH $out" | cut -c1-140
done
