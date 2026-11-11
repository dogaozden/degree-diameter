# For one (k, f): Delta = k + f. Scan primes n = 1 mod k downward from N_c; for each n and each r of order k:
# R = #{x : cov(x) >= 1}, mincov, meancov. Reports the largest n with full cover and the largest n with mincov >= 20.
import sys, time, json
import numpy as np
import abel
from abel import D
k = int(sys.argv[1]); f = int(sys.argv[2]); TBUD = float(sys.argv[3]) if len(sys.argv) > 3 else 90
U = np.load(f'U{k}.npy')
G = abel.zero_gen(f)
norms = np.abs(U).sum(axis=1); sums = U.sum(axis=1)
b = D - norms; t = 1 - sums
ok = (b >= 0) & (np.abs(t) <= D)
Gf = np.array([[float(G[i][j]) for j in range(2 * D + 1)] for i in range(D + 1)])
wt = np.where(ok, Gf[np.clip(b, 0, D), np.clip(t + D, 0, 2 * D)], 0.0)
Nc = wt.sum()
out = {'k': k, 'f': f, 'Delta': k + f, 'N_c': int(round(Nc))}
t0 = time.time()
def test(n, r):
    w = np.array([pow(r, i, n) for i in range(k)], dtype=np.int64)
    res = (U @ w) % n
    cov = np.bincount(res, weights=wt, minlength=n)
    return int((cov >= 1).sum()), float(cov.min()), float(cov.mean())
def primes_1mod(N):
    s = bytearray([1]) * (N + 1); s[0:2] = b'\x00\x00'
    for i in range(2, int(N ** 0.5) + 1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(N + 1) if s[i] and i % k == 1]
best_full = None; best20 = None
ps = primes_1mod(int(Nc))[::-1]
SKIPFULL = len(sys.argv) > 4 and sys.argv[4] == 'skipfull'  # R is f-independent: reuse the f=1 result
for n in ([] if SKIPFULL else ps):
    if time.time() - t0 > TBUD: out['timeout_full_at'] = n; break
    for r in abel.orders_k(n, k):
        R, mn, mean = test(n, r)
        if R == n:
            best_full = {'n': n, 'r': r, 'min': mn, 'mean': round(mean, 2)}; break
    if best_full is not None: break
# min coverage >= 20: mean >= 20 needed, so scan down from N_c/20
for n in [p for p in ps if p <= Nc / 20]:
    if time.time() - t0 > TBUD: out['timeout_min20_at'] = n; break
    for r in abel.orders_k(n, k):
        R, mn, mean = test(n, r)
        if mn >= 20:
            best20 = {'n': n, 'r': r, 'min': mn, 'mean': round(mean, 2)}; break
    if best20 is not None: break
out['largest_full'] = best_full; out['largest_min20'] = best20
out['time'] = round(time.time() - t0, 1)
print(json.dumps(out), flush=True)
