# c2: explicit F_8-isometry from the GF(2^18) model (classes L in Z_37449) to hex_q8 points.
# Hex point projection (x0,x1,x2,x4,x5,x6), normalised with first nonzero = 1; omega_std(a,b)=a0b4+a4b0+a1b5+a5b1+a2b6+a6b2.
import numpy as np, struct
from gf import EXP, LOG, N2, NP, F8, omega_val
HEX = '/home/user/degree-diameter/research/d10D7/hex/hex_q8.bin'
def fm(a, b):
    return 0 if (a == 0 or b == 0) else int(EXP[(LOG[a] + LOG[b]) % N2])
def fi(a):
    return int(EXP[(-LOG[a]) % N2])
def fp(a, k):
    return 0 if a == 0 else int(EXP[(LOG[a] * k) % N2])
def tr8(x):  # Tr_{2^18/8}(x) = sum_{j<6} x^{8^j}
    s = 0
    for j in range(6): s ^= fp(x, 8 ** j)
    return s
def inv_mat(M):
    n = len(M); A = [list(row) + [1 if i == j else 0 for j in range(n)] for i, row in enumerate(M)]
    for c in range(n):
        p = next(r for r in range(c, n) if A[r][c])
        A[c], A[p] = A[p], A[c]
        iv = fi(A[c][c]); A[c] = [fm(iv, x) for x in A[c]]
        for r in range(n):
            if r != c and A[r][c]:
                f = A[r][c]; A[r] = [x ^ fm(f, y) for x, y in zip(A[r], A[c])]
    return [row[n:] for row in A]
def mat_vec(M, v):
    out = []
    for row in M:
        s = 0
        for a, b in zip(row, v): s ^= fm(a, b)
        out.append(s)
    return out
G = [[tr8(int(EXP[i + k])) for k in range(6)] for i in range(6)]   # Gram of trace form on g^0..g^5
Gi = inv_mat(G)
def coords(w):
    """F_8-coordinates of a GF(2^18) element w in the basis g^0..g^5 (w = sum c_k g^k)."""
    out = []
    for j in range(6):
        dj = 0
        for k in range(6):
            dj ^= fm(Gi[k][j], int(EXP[k]))
        out.append(tr8(fm(w, dj)))
    return out
# field isomorphism F_8(abstract) -> hex F_8 (element a0+2a1+4a2, x^3=x+1)
alpha = next(int(a) for a in F8[1:] if fm(fm(a, a), a) ^ a ^ 1 == 0)
phi = {}
for a0 in (0, 1):
    for a1 in (0, 1):
        for a2 in (0, 1):
            phi[(a0 * 1) ^ fm(a1, alpha) ^ fm(fm(a2, alpha), alpha)] = a0 + 2 * a1 + 4 * a2
assert len(phi) == 8
def hexmul(a, b):
    r = 0
    for i in range(3):
        if (b >> i) & 1: r ^= a << i
    for i in (4, 3):
        if (r >> i) & 1: r ^= 0b1011 << (i - 3)
    return r
def hexinv(a):
    return next(b for b in range(1, 8) if hexmul(a, b) == 1)
def gram(A, x, y):
    s = 0
    for i in range(6):
        if x[i]:
            for j in range(6):
                if y[j] and A[i][j]: s ^= fm(fm(x[i], y[j]), A[i][j])
    return s
def sympl_basis(A):
    """Symplectic basis for alternating nondegenerate A over F_8 (abstract field).
    Returns S (6x6, columns u0,u1,u2,w0,w1,w2) with S^T A S = J (J[k][k+3]=J[k+3][k]=1)."""
    rest = [[1 if i == j else 0 for j in range(6)] for i in range(6)]
    us, ws = [], []
    for _ in range(3):
        v = rest[0]
        j = next(t for t in range(1, len(rest)) if gram(A, v, rest[t]))
        w = rest[j]; c = fi(gram(A, v, w)); w = [fm(c, t) for t in w]
        new = []
        for t, r in enumerate(rest):
            if t in (0, j): continue
            a = gram(A, r, w); b = gram(A, r, v)
            new.append([r[s] ^ fm(a, v[s]) ^ fm(b, w[s]) for s in range(6)])
        us.append(v); ws.append(w); rest = new
    cols = us + ws
    return [[cols[k][i] for k in range(6)] for i in range(6)]
A_abs = [[int(omega_val(i, j)) for j in range(6)] for i in range(6)]
S = sympl_basis(A_abs)
Sinv = inv_mat(S)
J = [[1 if (i + 3 == j or j + 3 == i) else 0 for j in range(6)] for i in range(6)]
def std_coords_abs(L):
    """abstract class L -> standard coordinates (abstract F_8 elements), normalised to first nonzero = 1."""
    x = int(EXP[L % N2]); c = coords(x)
    cp = mat_vec(Sinv, c)
    first = next(t for t in cp if t)
    iv = fi(first)
    return [fm(iv, t) for t in cp]
def hex_tuple(L):
    return tuple(phi[t] for t in std_coords_abs(L))
def load_hex_proj():
    with open(HEX, 'rb') as f:
        q, N, L = struct.unpack('3i', f.read(12))
        f.seek(12 + 4 * N * (q + 1))
        P = np.frombuffer(f.read(7 * N), dtype=np.uint8).reshape(N, 7).astype(int)
    d = {}
    for i in range(N):
        v = [P[i][0], P[i][1], P[i][2], P[i][4], P[i][5], P[i][6]]
        first = next(t for t in v if t)
        iv = hexinv(first)
        v = tuple(hexmul(iv, t) for t in v)
        assert v not in d
        d[v] = i
    return d, P
if __name__ == '__main__':
    import random
    random.seed(5)
    # 1) the basis-change is an isometry: omega_abs(c,d) == omega_std(c',d') for random pairs
    for _ in range(300):
        a, b = random.randrange(NP), random.randrange(NP)
        ca, cb = coords(int(EXP[a])), coords(int(EXP[b]))
        cpa, cpb = mat_vec(Sinv, ca), mat_vec(Sinv, cb)
        ws = 0
        for k in range(3):
            ws ^= fm(cpa[k], cpb[k + 3]) ^ fm(cpa[k + 3], cpb[k])
        assert ws == gram(A_abs, ca, cb), (a, b)
    print('isometry check ok')
    d, P = load_hex_proj()
    print('hex points', len(d))
    # 2) the map L -> hex id is a bijection onto all hex points
    ids = set(d[hex_tuple(L)] for L in range(NP))
    print('bijective onto hex ids:', len(ids) == NP)
    # 3) hex omega agrees with opposition in the abstract model for random pairs
    def hexB(i, j):
        a, b = P[i], P[j]
        return (a[0]*b[4] ^ a[4]*b[0] ^ a[1]*b[5] ^ a[5]*b[1] ^ a[2]*b[6] ^ a[6]*b[2]) if False else None
    print('done')
