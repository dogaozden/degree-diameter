"""Annealing screen of Haar graphs over metacyclic groups Z_m x|_r Z_k beyond the SmallGroups range.
Candidates: N = m k in [NMIN, NMAX], KMIN <= k <= KMAX, r^k = 1 mod m, r acting fixed-point-freely on Z_m (r != 1 mod
every prime p | m, so G' = Z_m and |G/G'| = k), action order >= 3; one r per orbit of r -> r^u (u in Z_k^*) and of
r -> r^-1 ... (only the first is used: it is an isomorphism).  The table is built with numpy and annealed with
hanneal.  Output: runs/metascreen_d{DELTA}D{D}.tsv (N m k r ord best_cost per seed best_set).
Usage: python3 metascreen.py DELTA D NMIN NMAX [--kmin 5] [--kmax 48] [--secs 30] [--seeds 1]"""
import argparse, os, subprocess
from math import gcd
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
SP = os.environ.get('SCRATCH', '/tmp/claude-0/-home-user-degree-diameter/2c3fb1ba-9359-5c52-a9c4-6d81a7db2df8/scratchpad')
def primes_of(n):
    out, d = [], 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0: n //= d
        d += 1
    if n > 1: out.append(n)
    return out
def order(r, m):
    x, o = r % m, 1
    while x != 1 % m:
        x = x * r % m; o += 1
    return o
def table(m, k, r, path):
    N = m * k
    rp = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    idx = np.arange(N); a = idx // k; j = idx % k
    with open(path, 'w') as f:
        f.write(f'{N} 0\n')
        for x in range(N):
            ax, jx = divmod(x, k)
            row = ((ax + rp[jx] * a) % m) * k + (jx + j) % k
            f.write(' '.join(map(str, row.tolist())) + '\n')
ap = argparse.ArgumentParser()
ap.add_argument('Delta', type=int); ap.add_argument('D', type=int); ap.add_argument('nmin', type=int); ap.add_argument('nmax', type=int)
ap.add_argument('--kmin', type=int, default=5); ap.add_argument('--kmax', type=int, default=48)
ap.add_argument('--secs', type=float, default=30); ap.add_argument('--seeds', type=int, default=1)
a = ap.parse_args()
outp = os.path.join(HERE, 'runs', f'metascreen_d{a.Delta}D{a.D}.tsv')
done = set()
if os.path.exists(outp):
    for l in open(outp):
        f = l.split('\t')
        if len(f) > 3: done.add((int(f[1]), int(f[2]), int(f[3])))
log = open(outp, 'a')
for N in range(a.nmin, a.nmax + 1):
    for k in range(a.kmin, a.kmax + 1):
        if N % k: continue
        m = N // k
        if m < 3: continue
        ps = primes_of(m); seen = set()
        for r in range(2, m):
            if gcd(r, m) != 1 or pow(r, k, m) != 1 or r in seen: continue
            seen |= {pow(r, u, m) for u in range(1, k) if gcd(u, k) == 1}
            if any(r % p == 1 for p in ps): continue
            o = order(r, m)
            if o < 3 or (m, k, r) in done: continue
            tab = os.path.join(SP, f'ms_{m}_{k}_{r}.txt')
            table(m, k, r, tab)
            costs, bset = [], '-'
            for s in range(1, a.seeds + 1):
                out = subprocess.run([os.path.join(HERE, 'hanneal'), tab, str(a.Delta), str(a.D), str(a.secs), str(s), '8',
                                      os.path.join(SP, f'ms_sol_{m}_{k}_{r}.txt')], capture_output=True, text=True).stdout
                res = [l for l in out.splitlines() if l.startswith('RESULT')][0].split()
                best = int(res[4].split('=')[1]); costs.append(best)
                if best == min(costs): bset = ' '.join(res[res.index('best_set') + 1:])
                if best == 0:
                    print(f'*** Z{m} x|_{r} Z{k} (N={N}): cost 0, S = {bset}', flush=True); break
            log.write(f'{N}\t{m}\t{k}\t{r}\t{o}\t{",".join(map(str, costs))}\t{bset}\n'); log.flush()
            os.remove(tab)
