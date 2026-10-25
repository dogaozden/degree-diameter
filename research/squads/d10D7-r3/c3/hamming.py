# Card c3, step 1: keep the same-vector matches of joint_cover, then match the leftover points to the leftover
# lines greedily by increasing Hamming distance between membership vectors (class-level, randomised within a distance).
import sys, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D7-r3/tools')
import numpy as np
from collections import defaultdict
from hexkit import Hex
HERE = '/home/user/degree-diameter/research/squads/d10D7-r3/c3'
t0 = time.time()
H = Hex(8); N = H.N
F = [tuple(map(int, r)) for r in np.load(HERE + '/F21.npy')]; K = len(F)
vp, vl = H.vectors(F)
freedP = np.zeros(N, bool); freedP[[p for p, l in F]] = True
freedL = np.zeros(N, bool); freedL[[l for p, l in F]] = True
cp = defaultdict(list); cl = defaultdict(list)
for u in range(N):
    if not freedP[u]: cp[vp[u]].append(u)
for L in range(N):
    if not freedL[L]: cl[vl[L]].append(L)
M = np.full(N, -1, np.int64)
for p, l in F: M[p] = l
exP = {}; exL = {}
for v in set(cp) | set(cl):
    a = cp.get(v, []); b = cl.get(v, []); m = min(len(a), len(b))
    for i in range(m): M[a[i]] = b[i]
    if len(a) > m: exP[v] = a[m:]
    if len(b) > m: exL[v] = b[m:]
pv = sorted(exP); lw = sorted(exL)
print('leftover point classes', len(pv), 'line classes', len(lw), 'leftover points', sum(len(exP[v]) for v in pv), flush=True)
POP = np.zeros(1 << K, np.int8); ar = np.arange(1 << K)
for b in range(K): POP += ((ar >> b) & 1).astype(np.int8)
pvA = np.array(pv, np.int64); lwA = np.array(lw, np.int64)
D = POP[pvA[:, None] ^ lwA[None, :]]
rem_p = np.array([len(exP[v]) for v in pv]); rem_l = np.array([len(exL[v]) for v in lw])
PE = [list(exP[v]) for v in pv]; LE = [list(exL[v]) for v in lw]
rng = np.random.default_rng(7); tot_ham = 0
for d in range(1, K + 1):
    I, J = np.nonzero(D == d)
    if len(I) == 0: continue
    perm = rng.permutation(len(I))
    for i, j in zip(I[perm].tolist(), J[perm].tolist()):
        if rem_p[i] == 0 or rem_l[j] == 0: continue
        m = min(int(rem_p[i]), int(rem_l[j]))
        for _ in range(m):
            M[PE[i].pop()] = LE[j].pop()
        rem_p[i] -= m; rem_l[j] -= m; tot_ham += d * m
    if rem_p.sum() == 0: break
assert (M >= 0).all() and len(set(M.tolist())) == N
Mb = np.load(HERE + '/M_base.npy')
ham_base = sum(int(POP[vp[u] ^ vl[int(Mb[u])]]) for u in range(N) if not freedP[u])
print('leftover Hamming sum: greedy', tot_ham, 'baseline zip', ham_base, flush=True)
U = H.uncovered(F, M); tot = sum(a + b for a, b in U)
print('greedy-Hamming uncovered total', tot, 'per pair', U, 'time', round(time.time() - t0, 1), flush=True)
np.save(HERE + '/M_hamming.npy', M)
