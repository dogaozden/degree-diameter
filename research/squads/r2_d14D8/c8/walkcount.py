"""walkcount.py BASEFILE SRC [T]: number of reduced walks (no immediate reuse of the same edge) of lengths 1,3,5,7
from point SRC to every line, in the base multigraph (edges as listed in BASEFILE: 'a b v' lines after header).
Products of group elements along reduced walks of length <= 7 (odd) are exactly what a (a,e)-lift can reach,
so a line needs >= m distinct reduced walks to be covered by a group of order m."""
import sys, numpy as np
fn, src = sys.argv[1], int(sys.argv[2])
T = int(sys.argv[3]) if len(sys.argv) > 3 else 7
data = np.loadtxt(fn, skiprows=1, dtype=np.int64, ndmin=2)
a, b = data[:, 0], data[:, 1]
E = len(a)
# directed edges: 0..E-1 = A->B (a->b), E..2E-1 = B->A (b->a) for the same undirected edge
tail = np.concatenate([a, E and b]); head = np.concatenate([b, a]) + 0
nA = int(a.max()) + 1; nB = int(b.max()) + 1
head = np.concatenate([b, a])  # B vertices indexed 0..nB-1 in head of A->B edges; A-indices for B->A edges
# vertex ids: A vertices 0..nA-1, B vertices nA..nA+nB-1
tailv = np.concatenate([a, nA + b]); headv = np.concatenate([nA + b, a])
rev = np.concatenate([np.arange(E) + E, np.arange(E)])
# out-edges of each vertex
x = np.zeros(2 * E, dtype=np.int64)
x[tailv == src] = 1  # walks starting at src (A vertex)
counts = {}
cur = x.copy()
for t in range(1, T + 1):
    # next: a walk of length t ends with directed edge e; extension e' needs tail(e') = head(e) and e' != rev(e)
    vert_count = np.zeros(nA + nB, dtype=np.int64)
    np.add.at(vert_count, headv, cur)
    if t % 2 == 1:
        # ends at B vertices (line side): counts per line
        lines = np.zeros(nB, dtype=np.int64)
        np.add.at(lines, headv[cur > 0] - nA, cur[cur > 0])
        counts[t] = lines
    nxt = np.zeros(2 * E, dtype=np.int64)
    # e' gets sum over e with head(e) = tail(e') minus the reverse edge contribution
    vc = vert_count[tailv]  # for each e', number of walks arriving at tail(e')
    nxt = vc - cur[rev]     # subtract walks whose last edge is the reverse of e' (rev(e') arrives at tail(e'))
    cur = nxt
tot = sum(counts.values())
print('lengths', sorted(counts), 'min over lines of total reduced walks (1,3,5,7):', int(tot.min()),
      'max', int(tot.max()), 'mean', round(float(tot.mean()), 1))
for t in sorted(counts):
    print(f'  length {t}: min {int(counts[t].min())} mean {counts[t].mean():.1f} max {int(counts[t].max())}')
hist = np.bincount(np.minimum(tot, 60))
print('histogram of totals (value:count, capped at 60):', {int(i): int(c) for i, c in enumerate(hist) if c})
