"""Rainbow design on H(q) (q prime) + 2 matchings, zero hexagon voltages.
psi_j(x) = iota_j(L_j(x)/L'_j(x)) in Z_m (ratio of two linear forms: a bijection on each nondegenerate line),
chi_j(y) = iota_j(Lam_j(y)/Lam'_j(y)) on lines via Pluecker coordinates (a bijection on each nondegenerate pencil),
M_j maps points of class c to lines of class c where possible (so psi_j(M_j^-1(y)) = chi_j(y) mostly).
python3 mk_ratio.py q m seed off1 off2 out [match]   (match=0: random M_j)"""
import sys, numpy as np
from hexlib import load, write_base, hex_edges
q, m, seed, off1, off2, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
match = int(sys.argv[7]) if len(sys.argv) > 7 else 1
N, LP, PL, coord = load(q)
rng = np.random.default_rng(seed)
X = coord.astype(np.int64)
inv = np.array([0] + [pow(int(a), q - 2, q) for a in range(1, q)])
def ratio(num, den):
    """values in 0..q (q = infinity), -1 if 0/0"""
    num %= q; den %= q
    r = (num * inv[den]) % q
    r = np.where(den == 0, q, r)
    return np.where((num == 0) & (den == 0), -1, r)
# Pluecker coordinates of lines from their first two points
A = X[LP[:, 0]]; B = X[LP[:, 1]]
pairs = [(i, j) for i in range(7) for j in range(i + 1, 7)]
PLK = np.stack([(A[:, i] * B[:, j] - A[:, j] * B[:, i]) % q for i, j in pairs], axis=1)
E = [hex_edges(LP)]
for j, off in enumerate((off1, off2)):
    L1, L2 = rng.integers(0, q, 7), rng.integers(0, q, 7)
    cp = ratio(X @ L1, X @ L2)
    G1, G2 = rng.integers(0, q, 21), rng.integers(0, q, 21)
    cl = ratio(PLK @ G1, PLK @ G2)
    # class sizes
    sp = np.bincount(cp + 1, minlength=q + 2); sl = np.bincount(cl + 1, minlength=q + 2)
    print(f'matching {j}: point classes {sp.tolist()}  line classes {sl.tolist()}', file=sys.stderr)
    M = np.full(N, -1)
    if match:
        freeL = []
        lines_by = {c: list(rng.permutation(np.flatnonzero(cl == c))) for c in range(-1, q + 1)}
        pts_by = {c: list(rng.permutation(np.flatnonzero(cp == c))) for c in range(-1, q + 1)}
        leftP = []
        for c in range(-1, q + 1):
            k = min(len(lines_by[c]), len(pts_by[c]))
            M[pts_by[c][:k]] = lines_by[c][:k]
            leftP += pts_by[c][k:]; freeL += lines_by[c][k:]
        freeL = rng.permutation(np.array(freeL, dtype=np.int64)); M[np.array(leftP, dtype=np.int64)] = freeL
        print(f'  mismatched points {len(leftP)}', file=sys.stderr)
    else:
        M = rng.permutation(N)
    psi = np.where(cp < 0, rng.integers(0, q + 1, N), cp) + off
    E.append(np.stack([np.arange(N), M, psi % m], axis=1))
write_base(out, N, m, np.concatenate(E))
