import sys, time, collections
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D5/r4/c8')
import relax, lns, numpy as np
S0 = lns.read_sol('/home/user/degree-diameter/research/squads/d10D5/r4/k10_orbit_100.sol')
F = S0['F']; sig = S0['sig']; H = S0['hubadj']
sinv = np.empty(lns.N, np.int64); sinv[sig] = np.arange(lns.N)
isfree = np.zeros(lns.N, bool); isfree[F] = True
base = lns.cover(F, sig, H, listing=True)[1]
print('base holes', base, flush=True)
X = [int(x) for x in np.nonzero(lns.PM[65] & ~isfree)[0]]
Ms = [int(M) for M in lns.LOF[69]]
t0 = time.time(); res = []
for x in X:
    for M in Ms:
        s = int(sinv[M])
        if s == x or isfree[s]: continue
        new = sig.copy(); new[x] = M; new[s] = sig[x]
        c3, _ = relax.cover_sub(F, new, H, [(3, 0)])
        if c3 != 0: continue
        cf, unc = lns.cover(F, new, H, listing=True)
        broken = collections.Counter((i, sd) for (i, sd, t) in unc)
        res.append((cf, x, s, M, dict(broken)))
print('swaps covering 69 (flag3 point side alone):', len(res), 'time %.1f' % (time.time() - t0), flush=True)
res.sort(key=lambda r: r[0])
for r in res[:8]: print(r, flush=True)
print('min full cost', res[0][0] if res else None, flush=True)
# how many of the 10 pairs break for the best swaps
cnt = collections.Counter()
for r in res:
    for k in r[4]: cnt[k] += 1
print('pairs appearing as broken in covering swaps:', cnt.most_common(12), flush=True)
