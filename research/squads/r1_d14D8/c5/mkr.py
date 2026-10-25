"""Ratio design for one matching (c5). Point psi(p) = iota(L(x)/L'(x)) with x = coordinates of p (rainbow on lines);
optional class matching M: point class c -> line class c, where line class chi(y) = ratio of Pluecker forms of y.
Hex voltages zero or random. Usage: python3 mkr.py OUT m seed matchmode(cls|rand) hexmode(zero|rand) [off]"""
import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/r1_d14D8/c5')
import mkd
from hexlib import load
q = 13
out, m, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
matchmode, hexmode = sys.argv[4], sys.argv[5]
off = int(sys.argv[6]) if len(sys.argv) > 6 else 0
N, LP, PL, coord = load(q)
rng = np.random.default_rng(seed)
X = coord.astype(np.int64)
inv = np.array([0] + [pow(int(a), q - 2, q) for a in range(1, q)])
def ratio(num, den):
    num %= q; den %= q
    r = (num * inv[den]) % q
    r = np.where(den == 0, q, r)
    return np.where((num == 0) & (den == 0), -1, r)
A = X[LP[:, 0]]; B = X[LP[:, 1]]
pairs = [(i, j) for i in range(7) for j in range(i + 1, 7)]
PLK = np.stack([(A[:, i] * B[:, j] - A[:, j] * B[:, i]) % q for i, j in pairs], axis=1)
L1, L2 = rng.integers(0, q, 7), rng.integers(0, q, 7)
cp = ratio(X @ L1, X @ L2)                         # point classes 0..13 (13 = infinity), -1 degenerate
psi = np.where(cp < 0, rng.integers(0, q + 1, N), cp)
if matchmode == 'cls':
    G1, G2 = rng.integers(0, q, 21), rng.integers(0, q, 21)
    cl = ratio(PLK @ G1, PLK @ G2)                 # line classes
    M = np.full(N, -1)
    freeL = []; leftP = []
    for c in range(-1, q + 1):
        lines_c = list(rng.permutation(np.flatnonzero(cl == c)))
        pts_c = list(rng.permutation(np.flatnonzero(cp == c)))
        k = min(len(lines_c), len(pts_c))
        M[np.array(pts_c[:k], dtype=np.int64)] = np.array(lines_c[:k], dtype=np.int64)
        leftP += pts_c[k:]; freeL += lines_c[k:]
    freeL = rng.permutation(np.array(freeL, dtype=np.int64))
    M[np.array(leftP, dtype=np.int64)] = freeL
    # repair: M must avoid incidences (points whose M-line is incident): random swaps
    bad = [p for p in range(N) if (PL[p] == M[p]).any()]
    for p in bad:
        for _ in range(100):
            r = int(rng.integers(N)); M[p], M[r] = M[r], M[p]
            if not (PL[p] == M[p]).any() and not (PL[r] == M[r]).any():
                break
            M[p], M[r] = M[r], M[p]
    print('class matching; mismatched points', len(leftP), 'incident repaired', len(bad), file=sys.stderr)
else:
    M = rng.permutation(N).astype(np.int64)
    bad = [p for p in range(N) if (PL[p] == M[p]).any()]
    for p in bad:
        for _ in range(100):
            r = int(rng.integers(N)); M[p], M[r] = M[r], M[p]
            if not (PL[p] == M[p]).any() and not (PL[r] == M[r]).any():
                break
            M[p], M[r] = M[r], M[p]
if hexmode == 'zero':
    hexvolt = np.zeros((N, q + 1), dtype=np.int64)
else:
    hexvolt = rng.integers(0, m, (N, q + 1))
F = mkd.get_F(N, PL, 1)
ls = np.repeat(np.arange(N), q + 1); ps = LP.reshape(-1).astype(np.int64)
mask = F[ps] != ls
hexE = np.stack([ps[mask], ls[mask], hexvolt.reshape(-1)[mask] % m], axis=1)
mE = np.stack([np.arange(N), M, (psi + off) % m], axis=1)
E = np.concatenate([hexE, mE]).astype(np.int64)
mkd.write_base_fast(out, N, m, E)
print('wrote', out, file=sys.stderr)
