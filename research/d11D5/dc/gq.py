"""W(8) geometry helpers: points (PG(3,8) normalized vectors), lines, polarity delta, collineations."""
import sys, json, random, os
D11 = "/home/user/degree-diameter/research/d11D5"
sys.path.insert(0, D11)
here = os.getcwd(); os.chdir(D11)
from dcover import load
n0, LINES, d_pt, d_ln, inv_ln = load(8); W = json.load(open("w8.json")); os.chdir(here)
from w8 import field
mul, finv = field(8)
PTS = [tuple(v) for v in W["points"]]; IDX = {v: i for i, v in enumerate(PTS)}
LSET = [frozenset(l) for l in LINES]; LIDX = {s: i for i, s in enumerate(LSET)}
PL = [[] for _ in range(n0)]
for li, l in enumerate(LINES):
    for p in l: PL[p].append(li)
def norm(v):
    for c in v:
        if c: s = finv[c]; return tuple(mul[s][x] for x in v)
def Bf(x, y): return mul[x[0]][y[1]] ^ mul[x[1]][y[0]] ^ mul[x[2]][y[3]] ^ mul[x[3]][y[2]]
def matvec(M, v): return tuple(mul[M[i][0]][v[0]] ^ mul[M[i][1]][v[1]] ^ mul[M[i][2]][v[2]] ^ mul[M[i][3]][v[3]] for i in range(4))
def matinv(M):
    A = [list(M[i]) + [1 if i == j else 0 for j in range(4)] for i in range(4)]
    for c in range(4):
        piv = next((r for r in range(c, 4) if A[r][c]), None)
        if piv is None: return None
        A[c], A[piv] = A[piv], A[c]
        iv = finv[A[c][c]]; A[c] = [mul[iv][x] for x in A[c]]
        for r in range(4):
            if r != c and A[r][c]:
                f = A[r][c]; A[r] = [A[r][k] ^ mul[f][A[c][k]] for k in range(8)]
    return [row[4:] for row in A]
def randmat(rng):
    while True:
        M = [[rng.randrange(8) for _ in range(4)] for _ in range(4)]
        if matinv(M) is not None: return M
def pmap(M):  # point permutation induced by M
    return [IDX[norm(matvec(M, p))] for p in PTS]
def span(x, y):
    s = set()
    for a in range(8):
        for b in range(8):
            if a or b:
                s.add(IDX[norm(tuple(mul[a][x[k]] ^ mul[b][y[k]] for k in range(4)))])
    return frozenset(s)
def is_W(ptset):  # PG-line (set of 9 point ids) totally isotropic?
    l = list(ptset); return Bf(PTS[l[0]], PTS[l[1]]) == 0
