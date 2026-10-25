import numpy as np, sys, os, random, time, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hexmod import Hex
SP = '/tmp/claude-0/-home-user-degree-diameter/0a251e0c-8f17-58ce-a4f2-34eda2ea0db1/scratchpad/'
H = Hex(SP + 'hex_q11.bin'); N = H.N; q = H.q
R = np.load(SP + 'R756idx.npy'); Rset = set(R.tolist())
colR = np.zeros(N, bool)
for r in R: colR[list(H.collinear_points(int(r)))] = True
inR = np.zeros(N, bool); inR[R] = True
def line_pts(u, v):
    U = H.X[u]; V = H.X[v]
    vecs = [(U + lam * V) % q for lam in range(q)] + [V]
    return H.index_of(np.array(vecs))
rng = random.Random(int(sys.argv[1])); ntr = int(sys.argv[2])
seen = set(); rows = []
allp = np.arange(N)
for trial in range(ntr):
    u = rng.randrange(N)
    B = H.Bmat(np.array([u]), allp)[0]
    cands = np.nonzero(B == 0)[0]
    cands = [int(v) for v in cands if v != u and int(v) not in H.collinear_points(u)]
    v = rng.choice(cands)
    T = tuple(sorted(line_pts(u, v).tolist()))
    if T in seen: continue
    seen.add(T); T = np.array(T)
    mm = H.collinear_points(int(T[0])) & H.collinear_points(int(T[1]))
    m = int(next(iter(mm)))
    orth = (H.Bmat(R, T) == 0)                         # 756 x 12
    tot = orth.sum(axis=1)
    c = orth.sum(axis=0)                               # c_t
    usable = ~colR[T] & ~inR[T]
    Tperp = int((tot == 12).sum())
    Rm = int(colR[m] and 0) 
    gm = [int(r) for r in R if r in H.collinear_points(m)]
    gm_T = []  # T-point each collinear base point is on
    for r in gm:
        t_on = [int(t) for t in T if int(t) in H.collinear_points(r)]
        gm_T.append((r, t_on))
    rows.append(dict(T=T.tolist(), m=m, usable=int(usable.sum()), cu=c[usable].tolist(), c=c.tolist(), Tperp=Tperp,
                     gm=len(gm), gm_inT=sum(1 for r, t in gm_T if t), gm_perp=sum(1 for r in gm if (H.Bmat(np.array([r]), T) == 0).all())))
print('T lines sampled', len(rows), flush=True)
print('usable points per T:', sorted(collections.Counter(r['usable'] for r in rows).items()))
print('Tperp (base pts in T^perp) per T:', sorted(collections.Counter(r['Tperp'] for r in rows).items()))
print('base pts collinear with m per T:', sorted(collections.Counter(r['gm'] for r in rows).items()))
print('base pts collinear with m, in T^perp:', sorted(collections.Counter(r['gm_perp'] for r in rows).items()))
print('c_t over all T points, distribution (min, max):', min(min(r['c']) for r in rows), max(max(r['c']) for r in rows))
allc = sorted(sum([r['cu'] for r in rows], []))
print('c_t for usable points: quantiles', np.percentile(allc, [0, 10, 25, 50, 75, 90, 100]).tolist() if allc else None)
best = sorted(rows, key=lambda r: (r['gm'] - r['gm_perp'], -r['usable']))[:5]
for r in best: print('best candidate: usable', r['usable'], 'gm', r['gm'], 'gm_perp', r['gm_perp'], 'Tperp', r['Tperp'], 'c', r['c'], 'm', r['m'], 'T', r['T'])
import pickle
pickle.dump(rows, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'tscan_%s.pkl' % sys.argv[1]), 'wb'))
