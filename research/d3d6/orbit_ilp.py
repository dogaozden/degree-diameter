"""Orbit ILP for the Theorem C copy problem on H(5) under a subgroup of SL(3,5) < G2(5).
python3 orbit_ilp.py group time_limit out.txt
group: s31 (Singer torus, order 31), s93 (31:3), s31x? ...
Writes a solution in hex_sa format (type id state) for hex_build.py."""
import itertools, sys
import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import lil_matrix
from hexgroup import perm_from_matrix, inv3, P, L, q

def mat_mul(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(3)) % q for j in range(3)] for i in range(3)]
def mat_pow(a, e):
    r = [[int(i == j) for j in range(3)] for i in range(3)]
    for _ in range(e): r = mat_mul(r, a)
    return r
def order(a):
    I = [[int(i == j) for j in range(3)] for i in range(3)]; r = a; k = 1
    while r != I: r = mat_mul(r, a); k += 1
    return k
def singer():
    for a, b, c in itertools.product(range(q), repeat=3):
        if c == 0: continue
        s = [[0, 0, c], [1, 0, b], [0, 1, a]]
        if order(s) == q ** 3 - 1: return s

def group_gens(name):
    if name == 'd16':
        return [[[2, 0, 0], [0, 1, 0], [0, 0, 3]], [[1, 0, 0], [0, 2, 0], [0, 0, 3]]]
    if name in ('c24', 'c24d'):
        # Singer cycle of GL(2,5) in the top-left block, det compensated in the corner
        for a, b in itertools.product(range(q), repeat=2):
            m = [[0, b], [1, a]]
            M = [[m[0][0], m[0][1], 0], [m[1][0], m[1][1], 0], [0, 0, 1]]
            det = (-b) % q; M[2][2] = pow(det, q - 2, q)
            if order(M) == 24:
                gens = [M]
                if name == 'c24d': gens.append([[2, 0, 0], [0, 2, 0], [0, 0, 4]])
                return gens
    if name == 'u25':
        return [[[1, 1, 0], [0, 1, 0], [0, 0, 1]], [[1, 0, 1], [0, 1, 0], [0, 0, 1]]]
    s = singer(); g31 = mat_pow(s, q - 1)
    gens = [g31]
    if name == 's93':
        # Frobenius: x -> x^q on GF(q^3) = GF(q)[s]; as a matrix in the basis 1, s, s^2 (columns = images)
        # build F with F e_j = (s^j)^q expressed in basis: use the vectors s^(qj) e_0
        e0 = [1, 0, 0]
        def apply(m, v): return [sum(m[i][k] * v[k] for k in range(3)) % q for i in range(3)]
        cols = []
        for j in range(3):
            m = mat_pow(s, q * j); cols.append(apply(m, e0))
        F = [[cols[j][i] for j in range(3)] for i in range(3)]
        det = inv3(F)[1]
        # scale to det 1 if possible (det is a cube?)
        for lam in range(1, q):
            if (pow(lam, 3, q) * det) % q == 1:
                F = [[(lam * x) % q for x in r] for r in F]; break
        assert inv3(F)[1] == 1
        gens.append(F)
    return gens

def orbits(perms, n):
    orb = [-1] * n; reps = []
    for i in range(n):
        if orb[i] >= 0: continue
        k = len(reps); reps.append(i); stack = [i]; orb[i] = k
        while stack:
            x = stack.pop()
            for p in perms:
                y = p[x]
                if orb[y] < 0: orb[y] = k; stack.append(y)
    return orb, reps

def main():
    name, tl, out = sys.argv[1], float(sys.argv[2]), sys.argv[3]
    gens = group_gens(name)
    pp = []; lpp = []
    for g in gens:
        r = perm_from_matrix(g); assert r is not None; pp.append(r[0]); lpp.append(r[1])
    N = len(P)
    op, rp = orbits(pp, N); ol, rl = orbits(lpp, N)
    no, nl = len(rp), len(rl)
    sizeP = [op.count(k) for k in range(no)]; sizeL = [ol.count(k) for k in range(nl)]
    print(f'{name}: {no} point orbits, {nl} line orbits', flush=True)
    thru = [[] for _ in range(N)]
    for j, l in enumerate(L):
        for p in l: thru[p].append(j)
    X, W, Y, T = 0, no, 2 * no, 2 * no + nl
    nv = 2 * no + 2 * nl
    rows = []; ub = []
    for k, j in enumerate(rl):          # line orbit k, representative j
        cx = {}; cw = {}
        for p in L[j]: cx[op[p]] = cx.get(op[p], 0) + 1
        rows.append(({X + o: c for o, c in cx.items()} | {T + k: -1}, 1))
        rows.append(({W + o: c for o, c in cx.items()}, 1))
    for k, p in enumerate(rp):
        cy = {}
        for j in thru[p]: cy[ol[j]] = cy.get(ol[j], 0) + 1
        rows.append(({Y + o: c for o, c in cy.items()} | {W + k: -1}, 1))
        rows.append(({T + o: c for o, c in cy.items()}, 1))
    for k in range(no): rows.append(({W + k: 1, X + k: -1}, 0))
    for k in range(nl): rows.append(({T + k: 1, Y + k: -1}, 0))
    A = lil_matrix((len(rows), nv))
    for r, (dct, b) in enumerate(rows):
        for v, c in dct.items(): A[r, v] += c
        ub.append(b)
    c = np.zeros(nv)
    for k in range(no): c[X + k] = -sizeP[k]
    for k in range(nl): c[Y + k] = -sizeL[k]
    res = milp(c=c, constraints=LinearConstraint(A.tocsr(), -np.inf, np.array(ub, float)),
               integrality=np.ones(nv), bounds=Bounds(0, 1), options={'time_limit': tl, 'disp': False})
    if res.x is None: print('no solution', res.status); return
    x = np.round(res.x).astype(int)
    tot = int(-c @ x); print(f'objective {tot} (bound {-res.mip_dual_bound if res.mip_dual_bound is not None else None}) status {res.status}', flush=True)
    with open(out, 'w') as f:
        for p in range(N):
            k = op[p]
            if x[X + k]: f.write(f'0 {p} {2 if x[W + k] else 1}\n')
        for j in range(N):
            k = ol[j]
            if x[Y + k]: f.write(f'1 {j} {2 if x[T + k] else 1}\n')

if __name__ == '__main__':
    main()
