#!/bin/bash
# cap_loop.sh: rounds of (score -> ban the elements of every pair that could not be served from pairing -> short dpack
# refill of the four bottleneck sets with the reduced masks, starting from the post-drop sets) for the relaxed (15,7)
# construction. usage: cap_loop.sh HEXBIN MIRROR_SOL BASEDIR DIR ROUNDS SECONDS DPACK
#   DIR holds P0.txt P1.txt S3.txt S4.txt (start) and mkmasks2.py; each round r writes DIR/r$r/.
set -e
H=$(readlink -f $1); MIR=$(readlink -f $2); BASE=$(readlink -f $3); DIR=$(readlink -f $4); R=$5; SEC=$6; DP=$(readlink -f $7)
D=$(dirname "$(readlink -f "$0")")
cd $DIR; touch banned.txt
cp P0.txt c_P0.txt; cp P1.txt c_P1.txt; cp S3.txt c_S3.txt; cp S4.txt c_S4.txt
for r in $(seq 1 $R); do
  python3 $D/score_relaxed.py $H $MIR $BASE c_P0.txt c_P1.txt c_S3.txt c_S4.txt r$r | tail -n 1
  awk '{print $3; print $4}' r$r/assign.sol.unserved.all 2>/dev/null >> banned.txt || true
  for f in P0 P1 S3 S4; do cp r$r/$f.txt c_$f.txt; done
  python3 mkmasks2.py c_P0.txt c_P1.txt c_S3.txt c_S4.txt > /dev/null
  python3 - <<PY
import numpy as np
b=set(np.loadtxt('banned.txt',dtype=np.int64,ndmin=1).tolist()) if open('banned.txt').read().strip() else set()
for f in ('allow_P2.txt','allow_S2.txt'):
    a=np.loadtxt(f,dtype=np.int64); np.savetxt(f,[x for x in a if x not in b],fmt='%d')
print('banned elements so far',len(b))
PY
  for f in P0 P1 S3 S4; do m=P; a=allow_P2.txt; [ ${f:0:1} = S ] && m=L && a=allow_S2.txt; (nice -n 5 $DP $H $m $((100*r+${#f}+${f:1:1})) $SEC c_$f.txt $a 0 n_$f.txt > n_$f.log 2>&1 &); done
  sleep $((SEC+5)); while pgrep -f "dpack $H" > /dev/null; do sleep 5; done
  for f in P0 P1 S3 S4; do cp n_$f.txt c_$f.txt; done
done
python3 $D/score_relaxed.py $H $MIR $BASE c_P0.txt c_P1.txt c_S3.txt c_S4.txt final | tail -n 1
