"""m-ovoids (exact) or maximum partial m-ovoids of P(W(q),x) by ILP (HiGHS via scipy.optimize.milp).

python3 movoid_ilp.py q m exact|max [time_limit] [mult]
  exact: find a set of points meeting every line in exactly m points (feasibility).
  max  : maximise the number of points with every line meeting the set in at most m points.
  mult : if given (an int k), allow each point up to k times (a multiset).
Writes runs/movoid_q{q}_m{m}_{mode}.json with the point list (indices into as_gq.build(q)).
"""
import json
import sys
import time
from pathlib import Path

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import lil_matrix

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from as_gq import build  # noqa: E402


def main():
    q, m, mode = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    tl = float(sys.argv[4]) if len(sys.argv) > 4 else 600
    mult = int(sys.argv[5]) if len(sys.argv) > 5 else 1
    F, pts, lines = build(q)
    n = len(pts)
    A = lil_matrix((len(lines), n))
    for j, L in enumerate(lines):
        for p in L:
            A[j, p] = 1
    A = A.tocsr()
    if mode == 'exact':
        cons = LinearConstraint(A, m, m)
        c = np.zeros(n)
    else:
        cons = LinearConstraint(A, 0, m)
        c = -np.ones(n)
    t0 = time.time()
    res = milp(c, constraints=[cons], integrality=np.ones(n), bounds=Bounds(0, mult),
               options={'time_limit': tl, 'disp': False})
    dt = time.time() - t0
    out = {'q': q, 'm': m, 'mode': mode, 'status': res.status, 'message': res.message, 'seconds': dt}
    if res.x is not None:
        x = np.round(res.x).astype(int)
        sel = [int(i) for i in range(n) for _ in range(x[i])]
        cnt = A @ x
        out.update(size=len(sel), points=sel, line_min=int(cnt.min()), line_max=int(cnt.max()),
                   bound=getattr(res, 'mip_dual_bound', None))
    print({k: v for k, v in out.items() if k != 'points'})
    (HERE / 'runs' / f'movoid_q{q}_m{m}_{mode}.json').write_text(json.dumps(out))


if __name__ == '__main__':
    main()
