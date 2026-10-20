"""D = 4, q even: W(q) (= Q(4,q) up to duality, self-dual for q even) with j copies of an ovoid and j copies of a
spread, copies joined by K_{j,j} between the copies of p and of the spread line through p: a (q+1+j)-regular
bipartite graph of diameter 4 on 2(q^2+1)(q+1+j) vertices.  Writes an edge list and runs bigcheck.

Model: V = GF(q^2)^2 over GF(q), B(x, y) = Tr(x1 y2 + x2 y1) (alternating in char 2); the regular spread
{ <x>_{GF(q^2)} } is totally isotropic; the ovoid is the singular set of an elliptic form Tr(x1 x2) + L(x)^2 with
polar form B (found by trying linear forms L).

python3 d4_even.py q j
"""
import itertools
import subprocess
import sys

import numpy as np

sys.path.insert(0, '/Users/dogaozden/AI_Projects/degree-diameter/research/evenq')
from hexq import Field, _tr2  # noqa: E402

BIGCHECK = '/Users/dogaozden/AI_Projects/research-lab/verify/bigcheck/bigcheck'
q, j = int(sys.argv[1]), int(sys.argv[2])
F = Field(q)
A, M, INV = F.ADD, F.MUL, F.INV
d = next(x for x in range(1, q) if _tr2(F, x) == 1)  # w^2 = w + d


def kmul(x, y):  # (a + b w)(c + e w), arrays of pairs along last axis
    a, b, c, e = x[..., 0], x[..., 1], y[..., 0], y[..., 1]
    return np.stack([A[M[a, c], M[d, M[b, e]]], A[A[M[a, e], M[b, c]], M[b, e]]], axis=-1)


# points of PG(3,q): GF(q)^4 vectors (a1, b1, a2, b2), normalised
vecs = np.array(list(itertools.product(range(q), repeat=4)), dtype=np.int64)[1:]
first = np.argmax(vecs != 0, axis=1)
pts = vecs[vecs[np.arange(len(vecs)), first] == 1]
N = len(pts)
assert N == (q + 1) * (q * q + 1)
POW = q ** np.arange(4)[::-1]
codes = pts @ POW
order = np.argsort(codes); pts, codes = pts[order], codes[order]


def idx(V):
    f = np.argmax(V != 0, axis=1)
    V = M[V, INV[V[np.arange(len(V)), f]][:, None]]
    i = np.searchsorted(codes, V @ POW)
    assert np.all(codes[i] == V @ POW)
    return i


def B(X, Y):  # Tr(x1 y2 + x2 y1) = w-coefficient
    x1, x2, y1, y2 = X[:, 0:2], X[:, 2:4], Y[:, 0:2], Y[:, 2:4]
    s = A[kmul(x1, y2), kmul(x2, y1)]
    return s[:, 1]


# totally isotropic lines: for each point p, the lines through p in p^perp
Bmat = np.array([B(pts, np.tile(e, (N, 1))) for e in np.eye(4, dtype=np.int64)]).T  # B(p, e_k)
lines = set()
for i in range(N):
    # points y with B(p, y) = 0
    by = A[A[M[pts[:, 0], Bmat[i, 0]], M[pts[:, 1], Bmat[i, 1]]], A[M[pts[:, 2], Bmat[i, 2]], M[pts[:, 3], Bmat[i, 3]]]]
    for y in np.nonzero(by == 0)[0]:
        if y <= i:
            continue
        L = idx(np.array([A[M[t, pts[i]], pts[y]] for t in range(q)] + [pts[i]]))
        lines.add(tuple(sorted(L.tolist())))
lines = sorted(lines)
assert len(lines) == N, len(lines)
lid = {L: k for k, L in enumerate(lines)}
through = [[] for _ in range(N)]
for k, L in enumerate(lines):
    for p in L:
        through[p].append(k)
assert all(len(t) == q + 1 for t in through)
# regular spread: GF(q^2)-multiples of each point
ws = np.array([[a, b] for a in range(q) for b in range(q) if (a, b) != (0, 0)])
spread = set()
for i in range(N):
    x1, x2 = pts[i, 0:2], pts[i, 2:4]
    V = np.concatenate([kmul(ws, np.tile(x1, (len(ws), 1))), kmul(ws, np.tile(x2, (len(ws), 1)))], axis=1)
    spread.add(tuple(sorted(set(idx(V).tolist()))))
spread = [lid[L] for L in spread]
assert len(spread) == q * q + 1
cov = np.zeros(N, int)
for k in spread:
    cov[list(lines[k])] += 1
assert np.all(cov == 1), 'not a spread'
# ovoid: singular points of Tr(x1 x2) + L(x)^2
x1x2 = kmul(pts[:, 0:2], pts[:, 2:4])[:, 1]
ovoid = None
for Lc in itertools.product(range(q), repeat=4):
    Lx = A[A[M[pts[:, 0], Lc[0]], M[pts[:, 1], Lc[1]]], A[M[pts[:, 2], Lc[2]], M[pts[:, 3], Lc[3]]]]
    Qv = A[x1x2, M[Lx, Lx]]
    O = np.nonzero(Qv == 0)[0]
    if len(O) == q * q + 1:
        inO = np.zeros(N, bool); inO[O] = True
        if all(inO[list(L)].sum() == 1 for L in lines):
            ovoid = O
            break
assert ovoid is not None
print(f'q={q}: W(q) {N} points/lines; spread {len(spread)} lines; ovoid {len(ovoid)} points (L = {Lc})', flush=True)
# graph: points 0..N-1, lines N..2N-1, point copies, line copies
sline = {}
for k in spread:
    for p in lines[k]:
        sline[p] = k
E = [(p, N + k) for k, L in enumerate(lines) for p in L]
base = 2 * N
pc = {(int(p), i): base + n for n, (p, i) in enumerate(itertools.product(ovoid, range(j)))}
base += len(pc)
lc = {(int(k), i): base + n for n, (k, i) in enumerate(itertools.product(spread, range(j)))}
n = base + len(lc)
for (p, i), u in pc.items():
    E += [(u, N + k) for k in through[p]]
    E += [(u, lc[(sline[p], i2)]) for i2 in range(j)]
for (k, i), u in lc.items():
    E += [(p, u) for p in lines[k]]
out = f'/Users/dogaozden/AI_Projects/degree-diameter/research/evenq/graphs/d4_q{q}_j{j}.txt'
with open(out, 'w') as fh:
    fh.write(f'{n}\n' + ''.join(f'{a} {b}\n' for a, b in E))
print(f'n = {n} (2(q^2+1)(q+1+j) = {2*(q*q+1)*(q+1+j)}), edges {len(E)} -> {out}', flush=True)
r = subprocess.run(['nice', '-n', '15', BIGCHECK, '-t', '4', out, str(q + 1 + j), '4'], capture_output=True, text=True)
print('\n'.join(l for l in r.stdout.splitlines() if l.split()[0] in ('degree', 'bipartite', 'VALID', 'INVALID')))
