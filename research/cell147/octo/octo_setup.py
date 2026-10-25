import numpy as np, sys, itertools, collections
sys.path.insert(0, '../mirror')
from hexmod import Hex
from octo_h import roots, refl   # roots doubled, refl(rd) mod 11
SP = '/tmp/claude-0/-home-user-degree-diameter/0a251e0c-8f17-58ce-a4f2-34eda2ea0db1/scratchpad/'
q = 11
H = Hex(SP + 'hex_oct11.bin')
p2, p4 = H.point_ball(0)
print('point ball sizes', len(p2), len(p4), '(want 132, 15972)')
l2, l4 = H.line_ball(0); print('line ball sizes', len(l2), len(l4))
X = H.X
def normalize(V):
    V = V % q; inv = np.array([0] + [pow(i, q - 2, q) for i in range(1, q)])
    first = np.argmax(V != 0, axis=1); return V * inv[V[np.arange(len(V)), first]][:, None] % q
def perm_of(M):
    img = normalize((M @ X.T).T); return H.index_of(img)
# W(E7) orbits on points via 7 reflections (in the 126 roots: use all for speed of closure)
gens = [refl(r) for r in roots[:126:9]] + [refl(r) for r in roots]
perms = [perm_of(M) for M in [refl(r) for r in roots]]
lab = -np.ones(H.N, dtype=np.int64); orbs = []
for s in range(H.N):
    if lab[s] >= 0: continue
    st = [s]; lab[s] = len(orbs); mem = [s]
    while st:
        x = st.pop()
        for p in perms:
            y = p[x]
            if lab[y] < 0: lab[y] = len(orbs); st.append(y); mem.append(y)
    orbs.append(mem)
print('W(E7) orbit sizes:', sorted(len(o) for o in orbs))
Rstar = np.array(sorted(next(o for o in orbs if len(o) == 756)))
G = X[Rstar]; Bm = (G @ G.T) % q; np.fill_diagonal(Bm, 1)
print('R* pairwise non-orthogonal:', bool((Bm != 0).all()))
np.save(SP + 'Rstar_oct.npy', Rstar)
# spread S*: lines inside u0^perp (x0 = 0)
inperp = (X[:, 0] % q == 0)
Sstar = np.array([l for l in range(H.N) if inperp[H.lp[l]].all()])
print('lines in u0^perp:', len(Sstar))
np.save(SP + 'Sstar_oct.npy', Sstar)
# H acts on lines?
Hm = np.load('H_best.npy')
ok = True
for M in Hm[:12]:
    pp = perm_of(M)
    for l in range(0, H.N, 997):
        img = set(pp[H.lp[l]].tolist()); c = set(H.pl[pp[H.lp[l][0]]].tolist())
        if not any(set(H.lp[m].tolist()) == img for m in c): ok = False; break
print('H maps hexagon lines to lines (sample):', ok)
