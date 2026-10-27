"""Pure + mixed extension, vectorised (THEOREM.md Lemma 3; see extend.py for the idea).
R pairwise opposite points, Sp pairwise opposite lines; add points X (pairwise opposite, not collinear with R) with
lines s_x (pairwise opposite, not in Sp, meeting exactly one spread line); S chosen inside Sp by cell counting.
usage: python3 extend2.py q RFILE SPREADFILE OUTPAIRS seed tries maxadd [maxn]"""
import sys, random, collections, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/projects/hexagon-family/tools'); from q6lib import Geo
q = int(sys.argv[1]); G = Geo(q); N = G.N; L = G.L
R = np.array([int(x) for x in open(sys.argv[2]).read().split()])
Sp = np.array([int(x) for x in open(sys.argv[3]).read().split()])
out = sys.argv[4]; seed = int(sys.argv[5]); rng = random.Random(seed); nrng = np.random.default_rng(seed)
tries = int(sys.argv[6]); maxadd = int(sys.argv[7]); maxn = int(sys.argv[8]) if len(sys.argv) > 8 else 10 ** 9
LP = G.LP; PL = G.PL
inR = np.zeros(N, bool); inR[R] = True
inSp = np.zeros(L, bool); inSp[Sp] = True
collR = np.zeros(N, bool); collR[LP[PL[R].ravel()].ravel()] = True
nx = np.zeros(N, dtype=np.int64)
for a in range(0, N, 20000):
    nx[a:a + 20000] = (G.B(G.C[a:a + 20000], G.C[R]) == 0).sum(1)
def near(s):
    """(lines within distance 4 of s as bool array, lines at distance 2 as index array)"""
    M = PL[LP[s]].ravel(); M = M[M != s]
    l4 = np.zeros(L, bool); l4[PL[LP[M].ravel()].ravel()] = True
    return l4, M
cand = np.nonzero(~inR & ~collR & (nx <= maxn))[0]
nrng.shuffle(cand); cand = cand[np.argsort(nx[cand], kind='stable')]
nonspread = np.nonzero(~inSp)[0]
X, Sx, Npat, Spat = [], [], [], []
forced = np.zeros(L, bool); l4s = []
rp = collections.Counter({(): len(R)})
def cells(np_list, sp_list, forcedmask):
    rc = collections.Counter(map(tuple, np.array(np_list).T)) if np_list else collections.Counter({(): len(R)})
    keep = ~forcedmask[Sp]
    sc = collections.Counter(map(tuple, np.array(sp_list).T[keep])) if sp_list else collections.Counter({(): int(keep.sum())})
    return all(c <= sc.get(T, 0) for T, c in rc.items())
XC = []
FEAS = int(sys.argv[9]) if len(sys.argv) > 9 else 10
def slack(np_list, sp_list, forcedmask):
    rc = collections.Counter(map(tuple, np.array(np_list).T))
    keep = ~forcedmask[Sp]
    sc = collections.Counter(map(tuple, np.array(sp_list).T[keep]))
    from math import lgamma
    tot = 0.0
    for T, c in rc.items():
        a = sc.get(T, 0)
        if c > a: return None
        tot += lgamma(a + 1) - lgamma(c + 1) - lgamma(a - c + 1)
    return round(tot, 3)
for x in cand:
    if X and (G.B(G.C[[x]], G.C[np.array(X)]) == 0).any(): continue
    npx = (G.B(G.C[[x]], G.C[R])[0] == 0)
    best = None; nfeas = 0
    for attempt in range(tries):
        s = int(nonspread[rng.randrange(len(nonspread))])
        l4, M = near(s)
        if any(l4[t] for t in Sx): continue
        conc = M[inSp[M]]
        if len(conc) != 1: continue
        pat = l4[Sp] & ~np.isin(Sp, conc)
        if pat.sum() < npx.sum(): continue
        f2 = forced.copy(); f2[conc] = True
        sl = slack(Npat + [npx], Spat + [pat], f2)
        if sl is not None:
            nfeas += 1
            if best is None or sl > best[0]: best = (sl, s, pat, f2)
            if nfeas >= FEAS: break
    if best is not None:
        sl, s, pat, f2 = best
        X.append(int(x)); Sx.append(s); Npat.append(npx); Spat.append(pat); forced = f2
        print('added x=%d (|N(x)|=%d) s=%d slack %s: |X| = %d' % (x, npx.sum(), s, sl, len(X)), flush=True)
    if len(X) >= maxadd: break
rpat = [tuple(int(Npat[i][j]) for i in range(len(X))) for j in range(len(R))]
bycell = collections.defaultdict(list)
for k, l in enumerate(Sp):
    if not forced[l]: bycell[tuple(int(Spat[i][k]) for i in range(len(X)))].append(int(l))
pairs = [(int(r), bycell[rpat[j]].pop()) for j, r in enumerate(R)] + list(zip(X, Sx))
open(out, 'w').write('\n'.join('%d %d' % p for p in pairs) + '\n')
print('RESULT q=%d |R|=%d + |X|=%d = %d' % (q, len(R), len(X), len(pairs)))
