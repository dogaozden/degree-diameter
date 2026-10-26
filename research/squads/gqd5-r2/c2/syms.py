"""Find symmetries of W(11) that preserve the regular spread S: (a) unipotent [[I,B],[0,I]] (B symmetric),
(b) diagonal diag(g, g^{-T}) with g in GL(2,11). Checked numerically on the collinearity graph and the spread partition.
Writes syms.json: list of point permutations (as lists)."""
import sys, json, itertools
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
import numpy as np, gqlib
from gqlib import GQ
q = 11
G = gqlib.W(q); F = G.F
S = gqlib.regular_spread_W(G); sline = json.load(open('struct.json'))['sline']
pts = G.coords; index = G.index
col = G.col
def perm_of(M):
    """M: 4x4 integer matrix over F_q acting on row vectors v -> v M (mod q, with field tables)"""
    out = []
    for v in pts:
        w = [0, 0, 0, 0]
        for j in range(4):
            acc = 0
            for i in range(4):
                acc = F.add[acc][F.mul[v[i]][M[i][j]]]
            w[j] = acc
        # normalise
        s = next(x for x in w if x)
        inv = F.inv[s]
        w = tuple(F.mul[inv][x] for x in w)
        out.append(index[w])
    return out
SL = np.array(sline)
def is_sym(p):
    p = np.array(p)
    img = np.full(G.nl, -1)
    for x in range(G.np):
        s0, s1 = SL[x], SL[p[x]]
        if img[s0] == -1: img[s0] = s1
        elif img[s0] != s1: return False
    for x in range(0, G.np, 97):
        if not np.array_equal(col[p[x]][p], col[x]): return False
    return True
found = []
# (a) unipotent
for b00, b01, b11 in itertools.product(range(q), repeat=3):
    M = [[1,0,b00,b01],[0,1,b01,b11],[0,0,1,0],[0,0,0,1]]
    p = perm_of(M)
    if is_sym(p) and np.array_equal(col[np.ix_(p, p)], col): found.append(('U', (b00,b01,b11), p))
print('unipotent preserving S:', sum(1 for f in found if f[0]=='U'), flush=True)
# (b) diagonal g, g^{-T}
def inv2(g):
    a,b,c,d = g
    det = F.sub[F.mul[a][d]][F.mul[b][c]]
    if det == 0: return None
    di = F.inv[det]
    return (F.mul[di][d], F.mul[di][F.neg[b]], F.mul[di][F.neg[c]], F.mul[di][a])  # row-major inverse
cnt = 0
for a,b,c,d in itertools.product(range(q), repeat=4):
    gi = inv2((a,b,c,d))
    if gi is None: continue
    # g^{-T}: transpose of inverse
    hT = (gi[0], gi[2], gi[1], gi[3])
    M = [[a,b,0,0],[c,d,0,0],[0,0,hT[0],hT[1]],[0,0,hT[2],hT[3]]]
    # g acts on (x0,x1) and h = g^{-T} on (x2,x3); verify symplectic: we only keep those that pass is_sym
    p = perm_of(M)
    if is_sym(p) and np.array_equal(col[np.ix_(p, p)], col): found.append(('D', (a,b,c,d), p)); cnt += 1
print('diagonal preserving S:', cnt, flush=True)
json.dump({'perms': [f[2] for f in found], 'labels': [[f[0], list(f[1])] for f in found]}, open('syms.json', 'w'))
print('total', len(found))
