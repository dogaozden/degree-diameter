import numpy as np, sys, collections
sys.path.insert(0, '../mirror')
from hexmod import Hex
SP = '/tmp/claude-0/-home-user-degree-diameter/0a251e0c-8f17-58ce-a4f2-34eda2ea0db1/scratchpad/'
q = 11
H = Hex(SP + 'hex_oct11.bin'); X = H.X; N = H.N
R = np.load(SP + 'Rstar_oct.npy'); S = np.load(SP + 'Sstar_oct.npy')
Hm = np.load('H_best.npy')
def normalize(V):
    V = V % q; inv = np.array([0] + [pow(i, q - 2, q) for i in range(1, q)])
    first = np.argmax(V != 0, axis=1); return V * inv[V[np.arange(len(V)), first]][:, None] % q
PP = np.array([H.index_of(normalize((M @ X.T).T)) for M in Hm])          # 96 x N point perms
# line perms: image of line l = the line containing the images of its first two points
lineof = {}
for l in range(N):
    a, b = H.lp[l][0], H.lp[l][1]; lineof[(min(a, b), max(a, b))] = l
def line_perm(pp):
    out = np.empty(N, dtype=np.int64)
    for l in range(N):
        a, b = pp[H.lp[l][0]], pp[H.lp[l][1]]
        out[l] = lineof.get((min(a, b), max(a, b)), -1)
    return out
# a line is determined by any two of its points; lineof only has the first two -> use incidence instead
pl = H.pl
def line_perm2(pp):
    out = np.empty(N, dtype=np.int64)
    for l in range(N):
        a, b = pp[H.lp[l][0]], pp[H.lp[l][1]]
        c = set(pl[a].tolist()) & set(pl[b].tolist()); out[l] = c.pop()
    return out
LP = np.array([line_perm2(pp) for pp in PP])
np.save(SP + 'oct_PP.npy', PP); np.save(SP + 'oct_LP.npy', LP)
def orbits(perms, elems):
    seen = {}; out = []
    for e in elems:
        if e in seen: continue
        orb = sorted(set(perms[:, e].tolist())); out.append(orb)
        for y in orb: seen[y] = len(out) - 1
    return out
oR = orbits(PP, R.tolist()); oS = orbits(LP, S.tolist())
print('H-orbits on R*:', sorted(collections.Counter(len(o) for o in oR).items()))
print('H-orbits on S*:', sorted(collections.Counter(len(o) for o in oS).items()))
colR = np.zeros(N, bool); colR[H.lp[H.pl[R]].reshape(-1)] = True; colR[R] = True
cand = np.nonzero(~colR)[0]
oC = orbits(PP, cand.tolist())
good = [o for o in oC if (lambda G: ((G @ G.T) % q + np.eye(len(o), dtype=np.int64)).all())(X[o])]
print('candidate point orbits:', len(oC), 'good (pairwise opposite):', len(good), 'sizes', sorted(collections.Counter(len(o) for o in good).items()))
np.save(SP + 'oct_goodpts.npy', np.array([o[0] for o in good]))
