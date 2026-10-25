"""DATA_CHECK.md numbers. Run from this folder: python3 data_check.py
Reads ../../frontier/sols/*.txt and ../../d5/sols/*.txt (same records as frontier/sizelaw/data.py, repo-relative)."""
import glob, os, math
import numpy as np
from groups_inv import from_header, meta, from_table_name, prod, cyc
HERE = os.path.dirname(os.path.abspath(__file__))
FR = os.path.join(HERE, '..', '..', 'frontier', 'sols'); D5 = os.path.join(HERE, '..', '..', 'd5', 'sols')

def Wlen(d, L): return 1 if L == 0 else d * (d - 1) ** (L - 1)          # reduced alternating words of length L
def W(d, D):  # words of the binding parity, length <= D-1 (= heuristic.py W = bipartite Moore bound per side)
    return sum(Wlen(d, L) for L in range(D) if L % 2 == (D - 1) % 2)
def moore_side(d, D): return sum((d - 1) ** i for i in range(D))

def mu_gen(d, D, N): return N * math.exp(-W(d, D) / N)
def mu_special(d, D, N, g):
    """Poisson mean of missed targets, THRESHOLD.md §3.4 (odd D: inverse pairs, involutions, central rotation orbits).
    Returns (mu_total, extra_over_generic)."""
    w = W(d, D)
    if D % 2 == 0: return N * math.exp(-w / N), 0.0
    k = (D - 1) // 2
    Z, I, Ic = g['Z'], g['inv'], g['inv_c']; Inc = I - Ic
    gen = (N - Z - Inc) * math.exp(-w / N)
    rot = sum(Wlen(d, 2 * j) / j for j in range(1, k + 1)) / N              # central: A and B merge, orbits of size 2j
    tot = gen + 2 * Inc * math.exp(-w / (2 * N)) + (Z - 1 - Ic) / 2 * math.exp(-rot) + Ic * math.exp(-rot / 2)
    return tot, tot - N * math.exp(-w / N)

def records():
    rows = []
    for f in sorted(glob.glob(FR + '/*.txt')):
        h = open(f).readline().split(); d, D = int(h[0]), int(h[1]); N = int(h[h.index('N') + 1])
        g = from_header(h); assert g['order'] == N, (f, g['order'], N)
        rows.append(dict(d=d, D=D, N=N, g=g, spec=' '.join(h[2:h.index('N')]), src=os.path.basename(f)))
    for f in sorted(glob.glob(D5 + '/*.txt')):
        h = open(f).readline().split(); d = int(h[0])
        if len(h) >= 5: N = int(h[1]); name = h[4].split('/')[-1][:-4]; g = from_table_name(name); spec = name
        else: m, k, r = map(int, h[1:4]); N = m * k; g = meta(m, k, r); spec = 'meta %d %d %d' % (m, k, r)
        assert g is None or g['order'] == N, (f, g, N)
        rows.append(dict(d=d, D=5, N=N, g=g, spec=spec, src='d5/' + os.path.basename(f)))
    # documented only in d5/REPORT.md (no sols file): order-176 group (structure not recorded), (Z19:Z3) x Z10
    rows.append(dict(d=5, D=5, N=176, g=None, spec='order-176 group (REPORT.md)', src='d5/REPORT.md'))
    rows.append(dict(d=7, D=5, N=570, g=prod(meta(19, 3, 7), cyc(10)), spec='(Z19:Z3) x Z10 (REPORT.md)', src='d5/REPORT.md'))
    for r in rows:
        d, D, N = r['d'], r['D'], r['N']; gD = (d - 1) ** 2 / ((d - 1) ** 2 - 1)
        r.update(W=W(d, D), C=N / (d - 1) ** (D - 2), gD=gD, lnN=math.log(N), mu=mu_gen(d, D, N))
        r['rho'] = r['W'] / (N * math.log(N))                   # theorem normalisation: threshold at rho -> 1
        r['ClnN'] = r['C'] * math.log(N) / (d * gD)
        if r['g'] is not None: r['mu_corr'], r['extra'] = mu_special(d, D, N, r['g'])
        else: r['mu_corr'], r['extra'] = r['mu'], float('nan')
    best = {}
    for r in rows:
        k = (r['d'], r['D'])
        if k not in best or r['N'] > best[k]['N']: best[k] = r
    for r in rows: r['best'] = best[(r['d'], r['D'])] is r
    return rows

def ols(x, y):
    A = np.vstack([np.ones_like(x), x]).T; c, *_ = np.linalg.lstsq(A, y, rcond=None); e = y - A @ c
    sd = e.std(ddof=2); cov = sd ** 2 * np.linalg.inv(A.T @ A)
    return c, np.sqrt(np.diag(cov)), e, sd

if __name__ == '__main__':
    rows = records(); B = sorted([r for r in rows if r['best']], key=lambda r: (r['D'], r['d']))
    assert all(W(d, D) == moore_side(d, D) for d in range(3, 20) for D in range(2, 12)), 'W != Moore/2'
    print('check: W(d,D) == bipartite Moore bound per side for d=3..19, D=2..11')
    print('records: %d files, %d cells' % (len(rows), len(B)))
    print('\n== best per cell ==')
    print(' cell    N            lnN    C_D    W/N    rho=W/(N lnN)  C lnN/(dg)  mu     mu_corr  extra/mu  group')
    for r in B:
        print('(%2d,%2d) %-12d %5.2f %6.3f %6.2f %7.3f %10.3f %8.1f %8.1f %8.3f  %s' % (r['d'], r['D'], r['N'], r['lnN'], r['C'], r['W'] / r['N'],
              r['rho'], r['ClnN'], r['mu'], r['mu_corr'], r['extra'] / r['mu'] if r['extra'] == r['extra'] else float('nan'), r['spec']))
    print('\n== per D (best per cell): C_D, C_D lnN/(d g), rho, ln mu ==')
    for D in sorted(set(r['D'] for r in B)):
        s = [r for r in B if r['D'] == D]
        f = lambda k: np.array([r[k] for r in s])
        print('D=%2d cells=%2d  C_D %.3f (sd %.3f)  C lnN/(dg) %.3f (sd %.3f)  rho %.3f  mean lnN %.2f  mean ln mu %.2f  1-<ln mu>/<lnN> %.3f' % (
            D, len(s), f('C').mean(), f('C').std(), f('ClnN').mean(), f('ClnN').std(), f('rho').mean(), f('lnN').mean(),
            np.log(f('mu')).mean(), 1 - np.log(f('mu')).mean() / f('lnN').mean()))
    x = np.array([r['lnN'] for r in B])
    for lab, key in (('mu (generic)', 'mu'), ('mu_corr (special targets)', 'mu_corr')):
        y = np.log([r[key] for r in B]); c, se, e, sd = ols(x, y)
        par = {p: e[[i for i, r in enumerate(B) if r['D'] % 2 == p]] for p in (0, 1)}
        print('\nfit ln %-26s = %.3f %+.3f lnN  (se %.3f, %.3f)  resid sd %.3f | parity mean resid even %+.3f odd %+.3f' % (
            lab, c[0], c[1], se[0], se[1], sd, par[0].mean(), par[1].mean()))
        y2 = np.array([r[key] for r in B]); c2, se2, e2, sd2 = ols(x, y2)
        print('    linear: %-20s = %.2f %+.2f lnN  (se %.2f, %.2f)  resid sd %.2f' % (lab, c2[0], c2[1], se2[0], se2[1], sd2))
    # without the small-N D=5 cells
    BB = [r for r in B if r['D'] >= 7]; x = np.array([r['lnN'] for r in BB])
    for key in ('mu', 'mu_corr'):
        c2, se2, e2, sd2 = ols(x, np.array([r[key] for r in BB]))
        print('D>=7 linear %-8s = %.2f %+.2f lnN (se %.2f, %.2f), resid sd %.2f' % (key, c2[0], c2[1], se2[0], se2[1], sd2))
    print('\n== odd-D files: special-target share (all files) ==')
    for r in sorted([r for r in rows if r['D'] % 2 and r['g'] is not None], key=lambda r: (r['D'], r['d'], -r['N'])):
        g = r['g']
        print('(%2d,%2d) N=%-10d |Z|=%-4d inv=%-6d (central %d)  mu=%6.2f  mu_corr=%6.2f  extra=%5.2f  %s%s' % (
            r['d'], r['D'], r['N'], g['Z'], g['inv'], g['inv_c'], r['mu'], r['mu_corr'], r['extra'], r['spec'], ' *best' if r['best'] else ''))
