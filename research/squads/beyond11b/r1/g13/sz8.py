# Build Sz(8) as the stabilizer of the Suzuki-Tits ovoid in PGL(4,8); write element matrices and inverse table.
import random, sys, struct
random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
POLY = 0b1011
def gmul(a, b):
    r = 0
    while b:
        if b & 1: r ^= a
        b >>= 1; a <<= 1
        if a & 8: a ^= POLY
    return r
MUL = [[gmul(a, b) for b in range(8)] for a in range(8)]
INV = [0] + [next(b for b in range(1, 8) if MUL[a][b] == 1) for a in range(1, 8)]
def pw(a, k):
    r = 1
    for _ in range(k): r = MUL[r][a]
    return r
def norm(v):
    for x in v:
        if x:
            i = INV[x]; return tuple(MUL[i][y] for y in v)
    raise ValueError
def mv(M, v):
    out = []
    for i in range(4):
        s = 0
        for j in range(4): s ^= MUL[M[i][j]][v[j]]
        out.append(s)
    return tuple(out)
def mm(A, B):
    R = []
    for i in range(4):
        row = []
        for j in range(4):
            s = 0
            for k in range(4): s ^= MUL[A[i][k]][B[k][j]]
            row.append(s)
        R.append(tuple(row))
    return tuple(R)
def normM(M):
    flat = [x for row in M for x in row]
    f = next(x for x in flat if x)
    i = INV[f]
    return tuple(tuple(MUL[i][x] for x in row) for row in M)
def det_rank_solve(cols, target):
    # solve sum lam_i cols_i = target over GF(8) (4x4), return lam or None
    A = [[cols[j][i] for j in range(4)] + [target[i]] for i in range(4)]
    r = 0; piv = []
    for c in range(4):
        p = next((k for k in range(r, 4) if A[k][c]), None)
        if p is None: return None
        A[r], A[p] = A[p], A[r]
        iv = INV[A[r][c]]; A[r] = [MUL[iv][x] for x in A[r]]
        for k in range(4):
            if k != r and A[k][c]:
                f = A[k][c]; A[k] = [A[k][t] ^ MUL[f][A[r][t]] for t in range(5)]
        r += 1
    return [A[i][4] for i in range(4)]
def inv_mat(M):
    # Gauss-Jordan inverse
    A = [list(M[i]) + [1 if i == j else 0 for j in range(4)] for i in range(4)]
    for c in range(4):
        p = next(k for k in range(c, 4) if A[k][c])
        A[c], A[p] = A[p], A[c]
        iv = INV[A[c][c]]; A[c] = [MUL[iv][x] for x in A[c]]
        for k in range(4):
            if k != c and A[k][c]:
                f = A[k][c]; A[k] = [A[k][t] ^ MUL[f][A[c][t]] for t in range(8)]
    return tuple(tuple(A[i][4 + j] for j in range(4)) for i in range(4))
sig = lambda x: pw(x, 4)
O = set()
for x in range(8):
    for y in range(8):
        z = MUL[x][y] ^ pw(x, 6) ^ sig(y)
        O.add(norm((1, x, y, z)))
O.add(norm((0, 0, 0, 1)))
O = sorted(O)
assert len(O) == 65, len(O)
Oset = set(O)
def det_nonzero(cols):
    return det_rank_solve(cols[:4], cols[4]) is not None and all(det_rank_solve(cols[:4], cols[4]))
def general(pts):
    lam = det_rank_solve(pts[:4], pts[4])
    return lam is not None and all(lam)
def frame_mat(pts):
    lam = det_rank_solve(pts[:4], pts[4])
    # columns lam_i * pts_i
    return tuple(tuple(MUL[lam[j]][pts[j][i]] for j in range(4)) for i in range(4))
A0 = None
while A0 is None:
    cand = random.sample(O, 5)
    if general(cand): A0 = cand
Af = frame_mat(A0); Afi = inv_mat(Af)
stab = []
tries = 0
while len(stab) < 4 and tries < 3000000:
    tries += 1
    B = random.sample(O, 5)
    if not general(B): continue
    M = mm(frame_mat(B), Afi)
    if all(norm(mv(M, o)) in Oset for o in O):
        stab.append(normM(M))
print("tries", tries, flush=True) if False else print("tries", tries, "hits", len(stab), file=sys.stderr)
# closure
gens = list({g for g in stab})[:4]
I = normM(tuple(tuple(1 if i == j else 0 for j in range(4)) for i in range(4)))
elems = [I]; idx = {I: 0}
q = [I]
while q:
    g = q.pop()
    for h in gens:
        k = normM(mm(g, h))
        if k not in idx:
            idx[k] = len(elems); elems.append(k); q.append(k)
print("group order", len(elems), file=sys.stderr)
if len(elems) == 29120:
    inv = [idx[normM(inv_mat(g))] for g in elems]
    with open(sys.argv[2] if len(sys.argv) > 2 else 'sz8.bin', 'wb') as f:
        f.write(struct.pack('<i', len(elems)))
        for g in elems:
            f.write(bytes(x for row in g for x in row))
        f.write(struct.pack('<%di' % len(inv), *inv))
    print("written", file=sys.stderr)
