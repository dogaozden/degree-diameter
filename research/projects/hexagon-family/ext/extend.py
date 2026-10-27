"""Pure + mixed extension (THEOREM.md Lemma 3). R: pairwise opposite points, Sp: pairwise opposite lines (a spread).
Add points X (pairwise opposite, none collinear with R) with lines s_x (pairwise opposite, not in Sp); then S is chosen
inside Sp with |S| = |R|. Lemma 3 holds iff, for every pattern T (the set of i with r in N(x_i), resp. L in
Gamma_4(s_i)), #R-points with pattern T <= #spread lines with pattern T (excluding the spread lines concurrent with
some s_i), and the X-X / s-s pairs are opposite. Greedy, smallest |N(x)| first.
usage: python3 extend.py q RFILE SPREADFILE OUTPAIRS [seed] [tries]"""
import sys, struct, random, collections, numpy as np
sys.path.insert(0, '../tools'); from q6lib import Geo
q = int(sys.argv[1]); G = Geo(q); N = G.N; L = G.L; Q1 = q + 1
R = [int(x) for x in open(sys.argv[2]).read().split()]
Sp = [int(x) for x in open(sys.argv[3]).read().split()]
out = sys.argv[4]; rng = random.Random(int(sys.argv[5]) if len(sys.argv) > 5 else 1)
tries = int(sys.argv[6]) if len(sys.argv) > 6 else 400
LP = G.LP; PL = G.PL
Rs = set(R); Sps = set(Sp); spidx = {l: i for i, l in enumerate(Sp)}
# points collinear with R
collR = np.zeros(N, dtype=bool)
for r in R:
    for l in PL[r]: collR[LP[l]] = True
BR = G.B(G.C, G.C[np.array(R)]) == 0          # N x |R|: orthogonal (distance <= 4)
nx = BR.sum(1)
def line_bfs(s):
    """distances (in the incidence graph) from line s to all lines, up to 6"""
    d = np.full(L, 99, dtype=np.int64); d[s] = 0; fr = [s]
    for step in (2, 4, 6):
        pts = set()
        for l in fr: pts.update(LP[l].tolist())
        nf = []
        for p in pts:
            for l in PL[p].tolist():
                if d[l] == 99: d[l] = step; nf.append(l)
        fr = nf
    return d
spl = np.array(Sp)
X, Sx, Npat, Spat, forced = [], [], [], [], set()
cand = [x for x in range(N) if x not in Rs and not collR[x]]
rng.shuffle(cand); cand.sort(key=lambda x: nx[x])
def feasible(npat_new, spat_new, forced_new):
    rp = collections.Counter(tuple(v) for v in np.array(npat_new).T) if npat_new else collections.Counter({(): len(R)})
    keep = np.array([l not in forced_new for l in Sp])
    sp = collections.Counter(tuple(v) for v in np.array(spat_new).T[keep]) if spat_new else collections.Counter({(): int(keep.sum())})
    return all(c <= sp.get(T, 0) for T, c in rp.items())
nonspread = [l for l in range(L) if l not in Sps]
for x in cand:
    if any(G.B(G.C[[x]], G.C[[y]])[0, 0] == 0 for y in X): continue
    npx = BR[x]
    for attempt in range(tries):
        s = rng.choice(nonspread)
        d = line_bfs(s)
        if any(d[t] != 6 for t in Sx): continue
        pat = d[spl] == 4
        if pat.sum() < npx.sum(): continue
        conc = [l for l in Sp if d[l] == 2]
        if len(conc) != 1: continue
        fn = forced | set(conc)
        if feasible(Npat + [npx], Spat + [pat], fn):
            X.append(x); Sx.append(s); Npat.append(npx); Spat.append(pat); forced = fn
            print('added x=%d (|N(x)|=%d) with s=%d: |X| = %d' % (x, npx.sum(), s, len(X)), flush=True)
            break
    if len(X) >= 200: break
# choose S and tau
rpat = [tuple(int(Npat[i][j]) for i in range(len(X))) for j in range(len(R))]
spat = {l: tuple(int(Spat[i][k]) for i in range(len(X))) for k, l in enumerate(Sp) if l not in forced}
bycell = collections.defaultdict(list)
for l, T in spat.items(): bycell[T].append(l)
pairs = []
for j, r in enumerate(R):
    pairs.append((r, bycell[rpat[j]].pop()))
pairs += list(zip(X, Sx))
open(out, 'w').write('\n'.join('%d %d' % p for p in pairs) + '\n')
print('RESULT q=%d |R|=%d + |X|=%d = %d' % (q, len(R), len(X), len(pairs)))
