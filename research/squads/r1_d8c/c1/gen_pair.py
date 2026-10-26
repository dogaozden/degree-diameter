"""c1: pair-sheet permutation lift of 5 levels of I(H(q)).

Usage: python3 gen_pair.py Q PHI RULE SEED OUT
  PHI  : random | index   (point p -> line phi(p) for the two matchings)
  RULE : a (other pairs matched in order) | rev (reversed order) | b (random bijection per flag)
Every element e (point or line) has k = (q+5)/2 sheets: 0 = A, 1 = B, 2+j = pair j of its q+1 neighbours
(neighbours are paired consecutively in the storage order of PL / LP, pair j = positions 2j, 2j+1).
Hexagon flag (p,L): A->A, B->B, pair(p,L) -> pair(L,p); the other (q-1)/2 pairs by RULE.
Matchings (level i): point (i,p,s) ~ line (i+1, phi(p), s) and ~ line (i+2 mod 5, phi(p), s): sheets by index.
Vertex ids: point (i,p,s) -> (i*2N + p)*k + s ; line (i,L,s) -> (i*2N + N + L)*k + s.
Output: explicit edge list for gcheck (first line n).  Level shift i -> i+1 is an automorphism, so
sources = level-0 vertices (range:0:2Nk) meet every orbit.
"""
import sys
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d10D8_work')
import hexlib

q = int(sys.argv[1]); phi_mode = sys.argv[2]; rule = sys.argv[3]; seed = int(sys.argv[4]); out = sys.argv[5]
MS = sys.argv[6] if len(sys.argv) > 6 else 'id'   # matching sheet map: id (literal) | swap (A<->B, pairs by index)
N, LP, PL, coord = hexlib.load(q)
L_ = LP.shape[0]
assert L_ == N
r = (q + 1) // 2           # pairs per element (q odd)
k = r + 2                  # sheets per element
LEV = 5
rng = np.random.default_rng(seed)

# position of line L in PL[p] (t), position of point p in LP[L] (u)
tpos = {}
for p in range(N):
    for t, L in enumerate(PL[p]):
        tpos[(p, int(L))] = t

def idp(i, p, s):
    return (i * 2 * N + p) * k + s

def idl(i, L, s):
    return (i * 2 * N + N + L) * k + s

edges = []
# hexagon edges
for L in range(N):
    for u, p in enumerate(LP[L]):
        p = int(p)
        j = tpos[(p, L)] // 2   # pair at p containing L
        jp = u // 2             # pair at L containing p
        perm = np.zeros(k, dtype=np.int64)
        perm[0] = 0; perm[1] = 1; perm[2 + j] = 2 + jp
        op = [x for x in range(r) if x != j]
        ol = [x for x in range(r) if x != jp]
        if rule == 'a':
            tgt = ol
        elif rule == 'rev':
            tgt = ol[::-1]
        elif rule == 'b':
            tgt = list(rng.permutation(ol))
        else:
            raise SystemExit('bad rule')
        for a, b in zip(op, tgt):
            perm[2 + a] = 2 + b
        assert sorted(perm.tolist()) == list(range(k))
        for i in range(LEV):
            for s in range(k):
                edges.append((idp(i, p, s), idl(i, L, int(perm[s]))))

# matchings
if phi_mode == 'random':
    phi = rng.permutation(N)
elif phi_mode == 'index':
    phi = np.arange(N)
else:
    raise SystemExit('bad phi')
taus = {}
for t in (1, 2):
    if MS == 'swap':
        taus[t] = [1 - s if s < 2 else s for s in range(k)]
    elif MS == 'perm':   # independent random sheet permutation per matching (seeded)
        taus[t] = [int(x) for x in rng.permutation(k)]
    else:
        taus[t] = list(range(k))
for p in range(N):
    for i in range(LEV):
        for s in range(k):
            edges.append((idp(i, p, s), idl((i + 1) % LEV, int(phi[p]), taus[1][s])))
            edges.append((idp(i, p, s), idl((i + 2) % LEV, int(phi[p]), taus[2][s])))

n = LEV * 2 * N * k
E = np.array(edges, dtype=np.int64)
assert E.shape[0] == len(edges)
deg = np.bincount(E.ravel(), minlength=n)
assert deg.min() == q + 3 and deg.max() == q + 3, (deg.min(), deg.max())
assert len(set(map(tuple, np.sort(E, axis=1)))) == len(E), 'multi-edge'
with open(out, 'w') as f:
    f.write(f'{n}\n')
    np.savetxt(f, E, fmt='%d')
print(f'MS={MS} wrote {out}: n={n} edges={len(E)} k={k} m={LEV*k} sources(level0)={2*N*k}')
