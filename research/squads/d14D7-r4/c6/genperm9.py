# genperm9.py SEED NMAT OUTPREFIX [MAXORD]: random isometries of V6 = {x4 = -C x0} over GF(9) (products of reflections
# r_v(x) = x - B(x,v)/Q(v) v, Q = x0x4+x1x5+x2x6-x3^2, B = polar form), as permutations of the 7300 points of E9.map.
# For each random product M with cycle lcm L, writes the powers M^(L/d) (order d, 2 <= d <= MAXORD) as permutation
# files OUTPREFIX_m{i}_d{d}.txt (one image per line, vertex order of E9.map). Prints the cycle type of M.
import sys, random
from math import gcd
ADD = [[0]*9 for _ in range(9)]; MUL = [[0]*9 for _ in range(9)]
for x in range(9):
    for y in range(9):
        a, b = x % 3, x // 3; c, d = y % 3, y // 3
        ADD[x][y] = (a + c) % 3 + 3*((b + d) % 3)
        MUL[x][y] = (a*c + 2*b*d) % 3 + 3*((a*d + b*c) % 3)
NEG = [0]*9; INV = [0]*9
for x in range(9):
    for y in range(9):
        if ADD[x][y] == 0: NEG[x] = y
        if MUL[x][y] == 1: INV[x] = y
C = 8
seed, nmat, outp = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
maxord = int(sys.argv[4]) if len(sys.argv) > 4 else 12
random.seed(seed)
pts = []; idx = {}
for line in open('E9.map'):
    v = list(map(int, line.split()))
    pts.append(v[2:9])
def norm(y):
    for k in range(7):
        if y[k]:
            iv = INV[y[k]]; return tuple(MUL[iv][t] for t in y)
    return None
for i, x in enumerate(pts): idx[norm(x)] = i
n = len(pts)
def add(a, b): return ADD[a][b]
def refl(v):
    v0, v1, v2, v3, v4, v5, v6 = v
    Qv = ADD[ADD[ADD[MUL[v0][v4]][MUL[v1][v5]]][MUL[v2][v6]]][NEG[MUL[v3][v3]]]
    assert Qv != 0
    iq = INV[Qv]
    c = [v4, v5, v6, NEG[MUL[2][v3]], v0, v1, v2]          # B(x,v) = sum_k c_k x_k
    R = [[0]*7 for _ in range(7)]
    for i in range(7):
        for k in range(7):
            t = MUL[MUL[v[i]][c[k]]][iq]
            R[i][k] = ADD[1 if i == k else 0][NEG[t]]
    return R
def matmul(A, B):
    return [[ (lambda i, j: __import__('functools').reduce(lambda s, k: ADD[s][MUL[A[i][k]][B[k][j]]], range(7), 0))(i, j)
              for j in range(7)] for i in range(7)]
def randV6():
    while True:
        v = [random.randrange(9) for _ in range(4)]
        x5, x6 = random.randrange(9), random.randrange(9)
        v = [v[0], v[1], v[2], v[3], NEG[MUL[C][v[0]]], x5, x6]
        Qv = ADD[ADD[ADD[MUL[v[0]][v[4]]][MUL[v[1]][v[5]]]][MUL[v[2]][v[6]]]][NEG[MUL[v[3]][v[3]]]]
        if Qv: return v
def apply(M, x):
    y = [0]*7
    for i in range(7):
        s = 0
        for k in range(7): s = ADD[s][MUL[M[i][k]][x[k]]]
        y[i] = s
    return y
def perm_of(M):
    out = [0]*n
    for i, x in enumerate(pts):
        j = idx.get(norm(apply(M, x)))
        assert j is not None, 'image not in E'
        out[i] = j
    return out
def cycles(p):
    seen = [False]*n; cyc = []
    for i in range(n):
        if not seen[i]:
            L = 0; j = i
            while not seen[j]: seen[j] = True; j = p[j]; L += 1
            cyc.append(L)
    return cyc
def lcm(a, b): return a*b//gcd(a, b)
for mi in range(nmat):
    k = random.randint(2, 6)
    M = [[1 if i == j else 0 for j in range(7)] for i in range(7)]
    for _ in range(k):
        M = matmul(M, refl(randV6()))
    p = perm_of(M)
    cyc = cycles(p)
    L = 1
    for c in cyc: L = lcm(L, c)
    hist = {}
    for c in cyc: hist[c] = hist.get(c, 0) + 1
    print('M%d k=%d order=%d cycles=%s' % (mi, k, L, sorted(hist.items())), flush=True)
    # powers of order d <= maxord
    pw = p[:]
    cur = list(range(n))
    for e in range(1, L):
        cur = [p[cur[i]] for i in range(n)]  # cur = p^e (unused, see below)
    done = set()
    for d in range(2, min(L, maxord) + 1):
        if L % d: continue
        e = L // d
        q2 = list(range(n))
        base = p[:]
        ee = e
        # compute p^e by repeated squaring
        res = list(range(n)); b = p[:]
        while ee:
            if ee & 1: res = [b[res[i]] for i in range(n)]
            b = [b[b[i]] for i in range(n)]; ee >>= 1
        fn = '%s_m%d_d%d.txt' % (outp, mi, d)
        with open(fn, 'w') as f:
            f.write('\n'.join(map(str, res)) + '\n')
        print('  wrote %s order %d' % (fn, d), flush=True)
