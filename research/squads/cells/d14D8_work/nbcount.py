"""Count nonbacktracking walks of length 1,3,5,7 from a source point to every line in a base graph (edge list file
as for lifteval, voltages ignored). Prints the distribution of the total per line, split by hexagon distance."""
import sys, numpy as np
from hexlib import load, dist_from_point
fn, q, nsrc = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
N, LP, PL, coord = load(q)
with open(fn) as f:
    nA, nB, m = map(int, f.readline().split())
E = np.loadtxt(fn, skiprows=1, dtype=np.int64)
a, b = E[:, 0], E[:, 1]
nE = len(a)
# arcs: 0..nE-1 = a->b, nE..2nE-1 = b->a ; vertex ids: points 0..N-1, lines N..2N-1
tail = np.concatenate([a, b + N]); head = np.concatenate([b + N, a])
rev = np.concatenate([np.arange(nE) + nE, np.arange(nE)])
rng = np.random.default_rng(5)
for s in rng.choice(N, nsrc, replace=False):
    w = (tail == s).astype(np.float64)
    tot = np.zeros(2 * N)
    tot += np.bincount(head, weights=w, minlength=2 * N)
    for k in range(2, 8):
        S = np.bincount(head, weights=w, minlength=2 * N)
        w = S[tail] - w[rev]
        if k % 2 == 1:
            tot += np.bincount(head, weights=w, minlength=2 * N)
    lt = tot[N:]
    dp, dl = dist_from_point(s, LP, PL)
    out = [f'src {s}: lines min {lt.min():.0f} mean {lt.mean():.1f}']
    for d in (1, 3, 5):
        sel = lt[dl == d]
        out.append(f'd{d}: n {len(sel)} min {sel.min():.0f} p1 {np.percentile(sel,1):.0f} med {np.median(sel):.0f}')
    print('; '.join(out))
