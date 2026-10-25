#!/bin/bash
# save_d7.sh Q EDGES NAME : write research/frontier/sols/NAME.sol (d7hex format) and check that d7hex rebuilds the
# identical edge list.  (job cell-13-7)
set -e
cd /home/user/degree-diameter/research/d13D7
python3 tools/to_d7hex_sol.py hex/hex_q$1.bin $2 hex/$3.sol
./hex/d7hex edges hex/hex_q$1.bin hex/$3.sol hex/_rt.edges > /dev/null 2>&1
python3 - $2 hex/_rt.edges <<'PY'
import sys, numpy as np
def canon(fn):
    with open(fn) as f:
        n = int(f.readline()); E = np.loadtxt(f, dtype=np.int64)
    E.sort(axis=1); return n, E[np.lexsort((E[:, 1], E[:, 0]))]
n1, A = canon(sys.argv[1]); n2, B = canon(sys.argv[2])
ok = n1 == n2 and A.shape == B.shape and bool((A == B).all())
print('d7hex round trip identical:', ok); sys.exit(0 if ok else 1)
PY
rm -f hex/_rt.edges; cp hex/$3.sol ../frontier/sols/
