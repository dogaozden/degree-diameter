import sys, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D5/r4')
import numpy as np
import lns
S = lns.read_sol('/home/user/degree-diameter/research/squads/d10D5/r4/k9_valid.sol')
F = S['F']; sig = S['sig'].copy(); A = S['hubadj']
k = len(F); N = lns.N
isfree = np.zeros(N, bool); isfree[F] = True
freeL = sig[F]
isfreeL = np.zeros(N, bool); isfreeL[freeL] = True
print('base cost', lns.cover(F, sig, A))
# per freed point: freed collinear count and freed-line concurrency
kap = {p: int(lns.PM[p, F].sum()) for p in F}
print('freed collinear counts', kap)
print('freed-line concurrency per freed line', {int(l): int(lns.LM[l, freeL].sum()) for l in freeL})
A10 = np.zeros((k + 1, k + 1), bool); A10[:k, :k] = A
rows = []
t0 = time.time()
for p in range(N):
    if isfree[p]: continue
    for l in lns.LOF[p]:
        l = int(l)
        if isfreeL[l]: continue
        q = int(np.nonzero(sig == l)[0][0])          # current preimage of l, gets p's old line
        sig2 = sig.copy(); sig2[p] = l; sig2[q] = sig[p]
        F2 = F + [p]
        c0 = lns.cover(F2, sig2, A10)
        kp = int(lns.PM[p, F].sum())                 # freed points collinear with p
        cl = int(lns.LM[l, freeL].sum())             # freed lines concurrent with l
        # old freed points that become more crowded (already had a freed collinear neighbour and get p)
        crowd = sum(1 for f in F if lns.PM[f, p] and kap_f_ok(f) ) if False else sum(1 for f in F if lns.PM[f, p] and lns.PM[f, F].sum() >= 1)
        rows.append((c0, kp, cl, crowd, p, l, q))
print('screened', len(rows), 'in', round(time.time() - t0, 1), 's')
rows.sort()
import collections
print('cost distribution', collections.Counter(r[0] for r in rows).most_common(12))
print('best by cover (c0, kappa, freedLconc, crowd, p, l, q):')
for r in rows[:25]: print(r)
rows2 = sorted(rows, key=lambda r: (r[1] > 2, r[2], r[1], r[0]))
print('by kappa<=2 then line conc:')
for r in rows2[:25]: print(r)
