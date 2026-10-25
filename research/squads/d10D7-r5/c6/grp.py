# GF(9)=GF(3)[i], i^2=-1, element e = c0 + 3*c1 (c0 const, c1 coeff of i). Quadric X0X4+X1X5+X2X6 = X3^2.
# Group: SL(3,9) Levi acting as (v,a,w) -> (g v, a, g^{-T} w). Element g of order 91 (semiregular on points).
import struct, sys, itertools, random, pickle
import numpy as np
FN = '/home/user/degree-diameter/research/d10D7/hex/hex_q9.bin'
data = open(FN, 'rb').read()
q, N, _ = struct.unpack_from('<iii', data, 0)
LP = np.frombuffer(data, dtype='<i4', count=N*10, offset=12).reshape(N, 10).copy()
C = np.frombuffer(data, dtype=np.uint8, count=7*N, offset=12+4*N*10).reshape(N, 7).astype(np.int64).copy()
def dec(e): return (e % 3, e // 3)
def enc(c0, c1): return (c0 % 3) + 3 * (c1 % 3)
ADD = np.zeros((9, 9), np.int64); MUL = np.zeros((9, 9), np.int64)
for a in range(9):
    for b in range(9):
        a0, a1 = dec(a); b0, b1 = dec(b)
        ADD[a, b] = enc(a0+b0, a1+b1)
        MUL[a, b] = enc(a0*b0 - a1*b1, a0*b1 + a1*b0)
NEG = np.array([[b for b in range(9) if ADD[a, b] == 0][0] for a in range(9)])
INV = np.array([0] + [[b for b in range(1, 9) if MUL[a, b] == 1][0] for a in range(1, 9)])
ONE = 1

def mm(A, B):
    R = [[0]*3 for _ in range(3)]
    for i in range(3):
        for j in range(3):
            s = 0
            for k in range(3): s = ADD[s, MUL[A[i][k], B[k][j]]]
            R[i][j] = int(s)
    return R
def mpow(A, k):
    R = [[int(i == j) for j in range(3)] for i in range(3)]
    B = A
    while k:
        if k & 1: R = mm(R, B)
        B = mm(B, B); k >>= 1
    return R
def is_id(A): return all(A[i][j] == (1 if i == j else 0) for i in range(3) for j in range(3))
def order(A, maxo=2000):
    B = A
    for k in range(1, maxo+1):
        if is_id(B): return k
        B = mm(B, A)
    return None
def companion(a, b, c):  # t^3 + a t^2 + b t + c  (x^3 = -a x^2 - b x - c)
    return [[0, 0, (-c) % 9 if False else int(NEG[c])], [1, 0, int(NEG[b])], [0, 1, int(NEG[a])]]
def has_root(a, b, c):
    for t in range(9):
        t2 = MUL[t, t]; t3 = MUL[t2, t]
        s = ADD[ADD[t3, MUL[a, t2]], ADD[MUL[b, t], c]]
        if s == 0: return True
    return False

def apply_map(g, gitT):
    # (v,a,w) -> (g v, a, gitT w)
    V = C[:, 0:3]; W = C[:, 4:7]
    NV = np.zeros_like(V); NW = np.zeros_like(W)
    for r in range(3):
        s = np.zeros(N, np.int64); t = np.zeros(N, np.int64)
        for k in range(3):
            s = ADD[s, MUL[g[r][k], V[:, k]]]
            t = ADD[t, MUL[gitT[r][k], W[:, k]]]
        NV[:, r] = s; NW[:, r] = t
    X = np.concatenate([NV, C[:, 3:4], NW], axis=1)
    return X

def normalize(X):
    # projective normalisation: first nonzero coordinate -> 1
    Y = X.copy()
    first = np.argmax(X != 0, axis=1)
    lead = X[np.arange(len(X)), first]
    inv = INV[lead]
    return MUL[inv[:, None], X]

W7 = 9 ** np.arange(7)
KEY = C @ W7
ORDER = np.argsort(KEY); SKEY = KEY[ORDER]
assert np.all(np.diff(SKEY) > 0)
def ids_of(X):
    keys = normalize(X) @ W7
    pos = np.searchsorted(SKEY, keys)
    assert np.all(SKEY[pos] == keys), 'image not a point'
    return ORDER[pos]

def is_line_set(perm):
    # check image of each line is a line (as set)
    lines = set(tuple(sorted(r)) for r in LP.tolist())
    img = perm[LP]
    bad = 0
    for r in img.tolist():
        if tuple(sorted(r)) not in lines: bad += 1
    return bad

if __name__ == '__main__':
    # bilinear check on lines: B(x,y) = X0Y4+X4Y0+X1Y5+X5Y1+X2Y6+X6Y2 + X3Y3 (since -2 = 1 mod 3)
    def B(x, y):
        s = np.zeros(len(x), np.int64)
        for (i, j) in [(0,4),(4,0),(1,5),(5,1),(2,6),(6,2)]:
            s = ADD[s, MUL[x[:, i], y[:, j]]]
        s = ADD[s, MUL[x[:, 3], y[:, 3]]]
        return s
    bad = 0
    for a in range(10):
        for b in range(a+1, 10):
            x = C[LP[:, a]]; y = C[LP[:, b]]
            bad += int(np.count_nonzero(B(x, y)))
    print('bilinear nonzero pairs on lines:', bad)
    # build element of order 91 in SL(3,9)
    random.seed(1)
    found = None
    for trial in range(2000):
        a, b, c = random.randrange(9), random.randrange(9), random.randrange(1, 9)
        if has_root(a, b, c): continue
        M = companion(a, b, c)
        g = mpow(M, 8)
        o = order(g, 200)
        if o == 91:
            found = (a, b, c, g); break
    a, b, c, g = found
    print('companion params', a, b, c, 'g =', g, 'order', order(g))
    gi = mpow(g, 90)
    assert is_id(mm(g, gi))
    gitT = [[gi[j][i] for j in range(3)] for i in range(3)]
    X = apply_map(g, gitT)
    perm = ids_of(X)
    print('perm is bijection:', len(np.unique(perm)) == N)
    print('lines not mapped to lines (variant A):', is_line_set(perm))
    pickle.dump({'g': g, 'gi': gi, 'perm': perm}, open('/home/user/degree-diameter/research/squads/d10D7-r5/c6/grp.pkl', 'wb'))
