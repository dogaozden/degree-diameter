#!/usr/bin/env python3
"""Hole anatomy for random symmetric S at (d,D)=(5,13), group fam x Z_n (fam = sl|psl, p prime, n prime).
Usage: classify.py fam p n [holesfile]   (default holes/<fam>_<p>_<n>.txt)
Classes of a hole x = (M, z):  central(z!=0)  [M = +-I, z != 0];  -I [SL, z = 0];  involution [PSL, trace 0, z = 0];
alpha-fixed [commutes with g up to sign, z = 0, not one of the above];  order4 [SL, trace 0, z = 0];  other.
Output: per class: class size |T| in G, hole entries per sample, miss rate per element per sample, and the fit
c = lambda / ln(1/rate) with lambda = W/N, so rate = exp(-lambda/c)."""
import sys, math, os
import numpy as np
fam, p, n = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
hf = sys.argv[4] if len(sys.argv) > 4 else os.path.join(os.path.dirname(os.path.abspath(__file__)), 'holes', f'{fam}_{p}_{n}.txt')
d, D = 5, 13
W = 1 + sum(d * (d - 1) ** (2 * i - 1) for i in range(1, (D - 1) // 2 + 1))
GM = p * (p * p - 1) if fam == 'sl' else p * (p * p - 1) // 2
N = GM * n
lam = W / N
# ---- class sizes via numpy enumeration of SL(2,p) ----
A, B, C = np.meshgrid(np.arange(p), np.arange(p), np.arange(p), indexing='ij')
A = A.ravel(); B = B.ravel(); C = C.ravel()
inv_a = np.array([pow(int(x), p - 2, p) if x else 0 for x in range(p)], dtype=np.int64)
sel = A != 0
a1, b1, c1 = A[sel], B[sel], C[sel]
d1 = ((1 + b1 * c1) % p) * inv_a[a1] % p
a0 = np.zeros(0, dtype=np.int64)
# a == 0: -bc = 1, d free
bb = np.arange(1, p, dtype=np.int64)
cc = (-np.array([pow(int(x), p - 2, p) for x in bb], dtype=np.int64)) % p
b0 = np.repeat(bb, p); c0 = np.repeat(cc, p); d0 = np.tile(np.arange(p, dtype=np.int64), len(bb))
Ma = np.concatenate([a1, np.zeros(len(b0), dtype=np.int64)])
Mb = np.concatenate([b1, b0]); Mc = np.concatenate([c1, c0]); Md = np.concatenate([d1, d0])
assert len(Ma) == p * (p * p - 1), (len(Ma), p * (p * p - 1))
trace0 = ((Ma + Md) % p == 0)
# alpha-fixed: g M g^-1 = +- M, g = [[0,-1],[1,-1]], g^-1 = [[-1,1],[-1,0]]
# compute g M g^-1 entrywise
def mul(a, b, c, dd, e, f, g_, h):
    return ((a * e + b * g_) % p, (a * f + b * h) % p, (c * e + dd * g_) % p, (c * f + dd * h) % p)
g = (0, p - 1, 1, p - 1); gi = (p - 1, 1, p - 1, 0)
def conj(Ma, Mb, Mc, Md):
    t = mul(0, p - 1, 1, p - 1, Ma, Mb, Mc, Md)
    return mul(*t, p - 1, 1, p - 1, 0)
ca, cb, cc_, cd = conj(Ma, Mb, Mc, Md)
same = (ca == Ma) & (cb == Mb) & (cc_ == Mc) & (cd == Md)
neg = (ca == (-Ma) % p) & (cb == (-Mb) % p) & (cc_ == (-Mc) % p) & (cd == (-Md) % p)
afix_M = same | neg if fam == 'psl' else same
centralM = ((Mb == 0) & (Mc == 0) & (Ma == Md) & ((Ma == 1) | (Ma == p - 1)))
if fam == 'psl':
    # PSL: M up to sign; SL count halved; identify classes on SL then divide by 2
    pass
def halve(x): return x // 2 if fam == 'psl' else x
size = {}
size['central_z'] = (2 * n - 2) if fam == 'sl' else (n - 1)    # (+-I, z!=0); PSL: identity coset with z!=0
size['-I'] = 1 if fam == 'sl' else 0
size['involution'] = halve(int(np.sum(trace0))) if fam == 'psl' else 0   # PSL involutions: trace 0 (SL pairs +-M)
size['order4'] = int(np.sum(trace0)) if fam == 'sl' else 0               # SL: trace 0 means M^2 = -I (order 4)
size['alpha-fixed'] = halve(int(np.sum(afix_M & ~centralM & ~trace0))) if fam == 'psl' else int(np.sum(afix_M & ~centralM & ~trace0))
size['other'] = N - sum(size.values())   # z = 0 and z != 0 non-central elements not in the classes above
# ---- parse holes ----
pat = None
samples = 0; entries = {}; per_sample = []
cur_cost = None; use = True
CMAX = int(os.environ.get('CMAX', '1000000000'))
with open(hf) as f:
    for line in f:
        if line.startswith('#'):
            parts = line.split(); cur_cost = int(parts[4]); use = cur_cost <= CMAX
            if use: samples += 1
            continue
        if not use: continue
        parts = line.split()
        if len(parts) < 3: continue
        # idx mat(a,b,c,d) z=Z side
        m = line[line.index('mat(') + 4:line.index(')')].split(',')
        a, b, c, dd = (int(x) % p for x in m)
        z = int(line.split('z=')[1].split()[0]) % n
        side = int(parts[-1])
        cent = (b == 0 and c == 0 and a == dd and a in (1, p - 1))
        if cent and z != 0: k = 'central_z'
        elif cent and z == 0: k = '-I' if (fam == 'sl' and a == p - 1) else ('identity' if fam == 'sl' else 'identity')
        elif z != 0: k = 'other'
        elif (a + dd) % p == 0 and fam == 'psl': k = 'involution'
        elif (a + dd) % p == 0 and fam == 'sl': k = 'order4'
        elif ((b == 0 and c == 0 and a == dd) or (False)): k = 'other'
        else:
            # alpha-fixed test: g M g^-1 == +-M
            t = mul(0, p - 1, 1, p - 1, a, b, c, dd); cc2 = mul(*t, p - 1, 1, p - 1, 0)
            fixed = cc2 == (a, b, c, dd) or (fam == 'psl' and cc2 == tuple((-x) % p for x in (a, b, c, dd)))
            k = 'alpha-fixed' if fixed else 'other'
        entries.setdefault(k, [0, 0]); entries[k][0] += 1; entries[k][1] += side
print(f"# {fam} p={p} n={n} N={N} vertices={2*N} W={W} lambda={lam:.4f} CMAX={CMAX} samples_used={samples}")
print(f"{'class':14s} {'|T|':>10s} {'entries':>10s} {'per_sample':>11s} {'B-side%':>8s} {'rate/elt/sample':>16s} {'fit c':>8s}")
tot_entries = sum(v[0] for v in entries.values())
for k in ['central_z', '-I', 'involution', 'order4', 'alpha-fixed', 'other', 'identity']:
    if k not in entries and k not in size: continue
    e, sb = entries.get(k, [0, 0])
    T = size.get(k, 1 if k == '-I' else 0)
    if k == 'other': T = size['other']
    if k == 'identity': T = 1
    ps = e / samples if samples else float('nan')
    rate = e / (samples * T) if (samples and T) else float('nan')
    fitc = lam / math.log(1 / rate) if (rate and 0 < rate < 1) else float('nan')
    print(f"{k:14s} {T:10d} {e:10d} {ps:11.2f} {100*sb/max(e,1):8.1f} {rate:16.3e} {fitc:8.2f}")
print("# total hole entries:", tot_entries, " enrichment = (entries share)/(|T|/N):")
for k in ['central_z', '-I', 'involution', 'order4', 'alpha-fixed']:
    if k in entries and size.get(k, 0):
        print(f"#   {k}: share {entries[k][0]/max(tot_entries,1):.4f} vs size share {size[k]/N:.3e}, enrichment {entries[k][0]/max(tot_entries,1)/(size[k]/N):.1f}")
