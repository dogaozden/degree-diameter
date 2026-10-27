"""Freed set with midpoints (THEOREM.md Lemma 3) -> d7hex .sol (sigma = local duality) and hub layouts.
Input PAIRS: lines "r s" (freed point r, its line s = tau(r)), hexgen2 indexing. Checks Lemma 3 (distances 4/6
preserved, midpoint -> midline map well defined and injective), builds sigma as in its proof, verifies (R2) at every
freed point, and writes
  PREFIX.sol             d7hex format: freed points, a 3-level hub graph (degree <= q-1), sigma
  PREFIX_LV{5,7}.hubs    xgen layouts: j = 2, 3 hubs per side per freed point, hub graph degree <= q-j
Every hub graph is checked: two same-type hubs whose owners are opposite are within 6 in the hub graph.
usage: python3 mixsol.py q PAIRS PREFIX seed [LVs e.g. 3,5,7]"""
import sys, random, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/projects/hexagon-family/tools'); from q6lib import Geo
q = int(sys.argv[1]); pairs = [tuple(map(int, l.split())) for l in open(sys.argv[2]) if l.strip()]
pre = sys.argv[3]; seed = int(sys.argv[4]); LVs = [int(x) for x in (sys.argv[5] if len(sys.argv) > 5 else '3').split(',')]
rng = random.Random(seed); G = Geo(q); N = G.N; L = G.L; LP = G.LP; PL = G.PL
R = np.array([p[0] for p in pairs]); S = np.array([p[1] for p in pairs]); K = len(R)
assert len(set(R.tolist())) == K and len(set(S.tolist())) == K
def G2p(r):  # points collinear with r
    a = LP[PL[r]].ravel(); return np.unique(a[a != r])
def G2l(s):  # lines concurrent with s
    a = PL[LP[s]].ravel(); return np.unique(a[a != s])
def near_l(s):  # lines within 4 of s
    m = np.zeros(L, bool); m[PL[LP[G2l(s)].ravel()].ravel()] = True; m[s] = True; return m
Bm = G.B(G.C[R], G.C[R]) == 0          # K x K, True = distance <= 4
np.fill_diagonal(Bm, False)
gp = [G2p(int(r)) for r in R]; gl = [G2l(int(s)) for s in S]
inR = np.zeros(N, bool); inR[R] = True
for i in range(K): assert not inR[gp[i]].any(), 'two freed points collinear'
inS = np.zeros(L, bool); inS[S] = True
for i in range(K): assert not inS[gl[i]].any(), 'two freed lines concurrent'
nl = [near_l(int(s)) for s in S] if K <= 3000 else None
mu = {}; muinv = {}
for i in range(K):
    for j in range(i + 1, K):
        dl4 = nl[i][S[j]]
        assert bool(Bm[i, j]) == bool(dl4), ('distance mismatch', i, j)
        if Bm[i, j]:
            m = np.intersect1d(gp[i], gp[j]); M = np.intersect1d(gl[i], gl[j])
            assert len(m) == 1 and len(M) == 1, ('midpoint', i, j, len(m), len(M))
            m, M = int(m[0]), int(M[0])
            assert mu.get(m, M) == M and muinv.get(M, m) == m, ('midpoint map inconsistent', i, j)
            mu[m] = M; muinv[M] = m
print('Lemma 3 holds: K = %d, midpoints %d' % (K, len(mu)), flush=True)
sig = np.full(N, -1, dtype=np.int64); used = np.zeros(L, bool)
def setsig(p, l):
    assert sig[p] in (-1, l) and (not used[l] or sig[p] == l), ('sigma clash', p, l)
    sig[p] = l; used[l] = True
for r, s in pairs: setsig(r, s)
for m, M in mu.items(): setsig(m, M)
for i in range(K):
    rp = [int(z) for z in gp[i] if sig[z] < 0]; rl = [int(l) for l in gl[i] if not used[l]]
    assert len(rp) == len(rl); rng.shuffle(rl)
    for z, l in zip(rp, rl): setsig(z, l)
fp = np.nonzero(sig < 0)[0].tolist(); fl = np.nonzero(~used)[0].tolist(); rng.shuffle(fl)
for z, l in zip(fp, fl): setsig(z, l)
assert (sig >= 0).all() and len(set(sig.tolist())) == N
for i in range(K): assert set(sig[gp[i]].tolist()) == set(gl[i].tolist()), ('R2 fails', i)
print('sigma built; (R2) verified at all %d freed points' % K, flush=True)
opp = ~Bm; np.fill_diagonal(opp, False)            # owners opposite
def hubgraph(j, d, tries=200):
    H = j * K; own = np.arange(H) % K
    need = opp[np.ix_(own, own)]                    # hub pairs that need NS distance <= 6
    for t in range(tries):
        E = set()
        for _ in range(d):
            perm = list(range(H)); rng.shuffle(perm); E.update((a, perm[a]) for a in range(H))
        A = np.zeros((H, H), dtype=np.float32)
        for a, c in E: A[a, c] = 1
        P = (A @ A.T > 0).astype(np.float32)        # same side distance <= 2 (V side)
        V6 = (P @ P @ P) > 0
        Q = (A.T @ A > 0).astype(np.float32); U6 = (Q @ Q @ Q) > 0
        if not (need & ~V6).any() and not (need & ~U6).any():
            return own, sorted(E)
    raise SystemExit('no hub graph for j=%d d=%d' % (j, d))
for LV in LVs:
    j = (LV - 1) // 2; d = q - j
    own, E = hubgraph(j, d)
    if LV == 3:
        with open(pre + '.sol', 'w') as f:
            f.write('d7hex %d %d %d %d\nfreed %s\n' % (q, N, K, 6 * N + 2 * K, ' '.join(map(str, R.tolist()))))
            f.write('hubedges %d %s\n' % (len(E), ' '.join('%d %d' % e for e in E)))
            for a in range(0, N, 20): f.write(' '.join(map(str, sig[a:a + 20].tolist())) + '\n')
        print('wrote %s.sol (n = %d)' % (pre, 6 * N + 2 * K))
    else:
        with open('%s_LV%d.hubs' % (pre, LV), 'w') as f:
            f.write('%d %d %d\n' % (j * K, j * K, len(E)))
            f.write(' '.join(map(str, own.tolist())) + '\n' + ' '.join(map(str, own.tolist())) + '\n')
            f.write('\n'.join('%d %d' % e for e in E) + '\n')
        print('wrote %s_LV%d.hubs (n = %d)' % (pre, LV, 2 * LV * N + 2 * j * K))
if 3 not in LVs:   # still write the .sol (sigma, freed) for xgen
    with open(pre + '.sol', 'w') as f:
        f.write('d7hex %d %d %d %d\nfreed %s\nhubedges 0\n' % (q, N, K, 6 * N + 2 * K, ' '.join(map(str, R.tolist()))))
        for a in range(0, N, 20): f.write(' '.join(map(str, sig[a:a + 20].tolist())) + '\n')
