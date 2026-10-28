#!/bin/bash
# runq.sh HEX SECS PORB...: orbit quotient + ILS for each point-orbit file; prints orbits and points of the best set.
HEX=$1; SECS=$2; shift 2
for P in "$@"; do
  T=${P%.porb}
  python3 orbquot.py $HEX $P $T.wg > $T.oq.log && python3 wg2csr.py $T.wg $T > /dev/null && timeout $((SECS+60)) ./mis3 $T $SECS 1 $T.ils.txt > $T.ils.log 2>&1
  python3 - $T <<'PY'
import sys, numpy as np
T = sys.argv[1]
tok = open(T + '.wg').read().split(); n = int(tok[0]); w = np.array(tok[1:n+1], dtype=int)
S = np.array(open(T + '.ils.txt').read().split(), dtype=int)
print(T, 'quotient', n, 'orbits', len(S), 'points', int(w[S].sum()), flush=True)
PY
done
