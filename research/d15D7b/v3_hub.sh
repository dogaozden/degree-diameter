#!/bin/bash
# v3_hub.sh: hub graph for a typedmirror3 .sol: random unequal-sides graph (hubgen.py), then rounds of
# build + BFS from all hubs and paired-element vertices (hubfar.c) + aimed 2-switches (hubfix.py) until no far pair.
# usage: v3_hub.sh HEXBIN SOL_NOHUB OUT.sol THREADS   (needs ./hubfar compiled from research/d15D7b/hubfar.c in the cwd)
set -e
D=$(dirname "$(readlink -f "$0")")
HEX=$1; S0=$2; OUT=$3; T=${4:-4}
read KB KA < <(awk '$1=="hubs"{print $2, $3; exit}' $S0)
N=177156; NV0=$((14*N))
python3 $D/hubgen.py $KB $KA 8 1 he_0.txt
for r in 0 1 2 3 4 5 6 7; do
  python3 $D/tm3_build.py sethub $S0 he_$r.txt cur.sol > /dev/null
  python3 $D/tm3_build.py build $HEX cur.sol cur.edges cur.src > build_$r.log
  ./hubfar cur.edges 7 $T cur.src > far_$r.txt
  tail -n 1 far_$r.txt
  if grep -q "far_pairs=0 " far_$r.txt; then cp cur.sol $OUT; echo "done: $OUT"; exit 0; fi
  python3 $D/hubfix.py he_$r.txt far_$r.txt $NV0 $KB $((r+1)) he_$((r+1)).txt
done
echo "no convergence"; exit 1
