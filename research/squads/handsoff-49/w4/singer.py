# singer.py: automorphisms of the PG(2,3) incidence graph (base pg23.txt: points 0..12, lines 13..25) of order 13
# (Singer cycles), written as permutations of the 26 vertices, fixed-point-free ones to auts_pg13.txt
import itertools
pts = []
for v in itertools.product(range(3), repeat=3):
    if v == (0, 0, 0): continue
    nz = [c for c in v if c]
    if nz[0] == 1: pts.append(v)
def norm(v):
    v = tuple(x % 3 for x in v)
    nz = [c for c in v if c]
    inv = 1 if nz[0] == 1 else 2
    return tuple((inv * x) % 3 for x in v)
idx = {p: i for i, p in enumerate(pts)}
E = set()
for l in open('pg23.txt').read().split('\n')[1:]:
    if l.strip():
        u, v = map(int, l.split()); E.add((u, v))
def mat_mul(A, v):
    return tuple(sum(A[i][j]*v[j] for j in range(3)) % 3 for i in range(3))
def det3(A):
    return (A[0][0]*(A[1][1]*A[2][2]-A[1][2]*A[2][1]) - A[0][1]*(A[1][0]*A[2][2]-A[1][2]*A[2][0]) + A[0][2]*(A[1][0]*A[2][1]-A[1][1]*A[2][0])) % 3
def transpose_inv(A):
    # inverse of A^T for det != 0 over F_3 by brute force
    for B in itertools.product(range(3), repeat=9):
        M = [list(B[0:3]), list(B[3:6]), list(B[6:9])]
        # check M * A^T == I
        ok = True
        for i in range(3):
            for j in range(3):
                s = sum(M[i][k]*A[j][k] for k in range(3)) % 3
                if s != (1 if i == j else 0): ok = False; break
            if not ok: break
        if ok: return M
    return None
found = []
cnt = 0
for B in itertools.product(range(3), repeat=9):
    A = [list(B[0:3]), list(B[3:6]), list(B[6:9])]
    if det3(A) == 0: continue
    # point permutation
    pp = [idx[norm(mat_mul(A, p))] for p in pts]
    # order of the induced permutation on points
    seen = [False]*13; orders = []
    for s in range(13):
        if seen[s]: continue
        L = 0; x = s
        while not seen[x]: seen[x] = True; x = pp[x]; L += 1
        orders.append(L)
    if sorted(orders) != [13]: continue
    # dual action on lines: l -> (A^{-1})^T l ; A^{-T} : use A^{-T} via brute inverse of A^T
    Ainv_T = transpose_inv(A)
    if Ainv_T is None: continue
    lp = [idx[norm(mat_mul(Ainv_T, p))] for p in pts]
    perm = pp + [13 + x for x in lp]
    # check automorphism
    ok = all(((perm[u], perm[v]) in E or (perm[v], perm[u]) in E) for (u, v) in E)
    if not ok: continue
    found.append(perm)
    cnt += 1
    if cnt >= 3: break
print("singer automorphisms found:", len(found))
with open('auts_pg13.txt', 'w') as f:
    for p in found:
        f.write(' '.join(map(str, p)) + '\n')
