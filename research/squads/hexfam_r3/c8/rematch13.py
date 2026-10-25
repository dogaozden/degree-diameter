import sys, numpy as np
from collections import defaultdict
sys.path.insert(0, '/home/user/degree-diameter/research/projects/hexagon-family/tools'); from q6lib import Geo
G = Geo(13); N, L = G.N, G.L; LP, PL = G.LP, G.PL
pairs = [tuple(map(int, l.split())) for l in open('disj13_try1.pairs') if l.strip()]
R = np.array([int(v) for v in open('/home/user/degree-diameter/research/d10D7/sets/P13_E7sub_E6_792.txt').read().split()])
Sp = np.array([int(v) for v in open('/home/user/degree-diameter/research/d10D7/sets/L13_spread.txt').read().split()])
inSp = np.zeros(L, bool); inSp[Sp] = True
X = [p[0] for p in pairs[792:]]; S = [p[1] for p in pairs[792:]]
def l4(s):
    M = PL[LP[s]].ravel(); M = M[M != s]
    m = np.zeros(L, bool); m[PL[LP[M]].ravel()] = True; return m, M
conc = []; hits = []
for s in S:
    m, M = l4(s); cm = M[inSp[M]]; assert len(cm) <= 1
    conc.append(int(cm[0]) if len(cm) == 1 else -1)
    h = np.nonzero(m & inSp)[0]; hits.append(set(h[h != conc[-1]].tolist()))
removed = set(c for c in conc if c >= 0)
Rnb = [set(np.nonzero(G.B(G.C[[x]], G.C[R])[0] == 0)[0].tolist()) for x in X]  # indices into R
pat_R = {i: frozenset(k for k in range(len(X)) if i in Rnb[k]) for i in range(len(R))}
pat_L = defaultdict(list)
for l in Sp:
    l = int(l)
    if l in removed: continue
    pat_L[frozenset(k for k in range(len(S)) if l in hits[k])].append(l)
byc = defaultdict(list)
for i in range(len(R)): byc[pat_R[i]].append(int(R[i]))
out = []; ok = True
for T, rs in byc.items():
    ls = pat_L.get(T, [])
    if len(ls) < len(rs): print('cell fail', sorted(T), len(rs), len(ls)); ok = False; break
    out += list(zip(rs, ls))
print('cells', len(byc), 'ok', ok)
if ok:
    out += list(zip(X, S))
    open('disj13_fixed.pairs', 'w').write('\n'.join('%d %d' % p for p in out) + '\n'); print('wrote', len(out))
