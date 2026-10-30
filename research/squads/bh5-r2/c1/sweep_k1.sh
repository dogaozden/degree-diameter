#!/bin/bash
# c1 sweep: bi-coset (5,5), h=2, H=K involution (non-central), exhaustive when count <= MAXC else sampled.
# usage: sweep_k1.sh ORDERS...   (group tables in groups/, output in out/, log in sweep_k1.log)
cd /home/user/degree-diameter/research/squads/bh5-r2/c1
for o in "$@"; do
  for f in groups/s_${o}_*.txt; do
    b=$(basename $f .txt)
    timeout 120 nice -n 10 ./bicoset_k1 $f 2 5 20 ${MAXC:-30000} 1 out/$b.edges 2>&1 | grep -v '^CLASS' | grep -E '^(GROUP|BEST|VALID|SKIP)' | sed "s|^|$o |"
  done
done
echo SWEEP_DONE
