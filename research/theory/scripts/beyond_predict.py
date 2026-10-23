"""BEYOND_RANDOM.md §3: predicted gain in N from alpha-invariant (k = 3) S, checked against the orbit records.
Run from this folder: python3 beyond_predict.py   (output: beyond_predict_out.txt)

Data: orb_runs.txt (every haar_sym ORBIT run of the structured job), cmp_runs.txt (its random-vs-orbit head-to-head),
and the random-S records in ../../frontier/sols (files without 'orb' in the name)."""
import glob, math, os, re
import numpy as np
from orbit_model import parse_group, group_invariants, alpha_data, mu_rand, mu_orbit, lam
from model import W
from groups_inv import from_header

HERE = os.path.dirname(os.path.abspath(__file__))
SOLS = os.path.join(HERE, '..', '..', 'frontier', 'sols')
RX = re.compile(r'd=(\d+) D=(\d+) group=(.*) N=(\d+) best=(\d+) evals=(\d+) time=([\d.]+)(?: orbit k=(\d) m=(\d) f=(\d) fix=(\d+))?')

def load_runs(fn):
    out = []
    for line in open(os.path.join(HERE, fn)):
        if line.startswith('#'): continue
        m = RX.search(line)
        if not m: continue
        d, D, spec, N, best, ev, t, k, mm, f, fix = m.groups()
        Qs, n = parse_group(spec); g = group_invariants(Qs, n)
        r = dict(d=int(d), D=int(D), spec=spec, N=int(N), best=int(best), evals=int(ev), time=float(t), g=g,
                 orbit=k is not None)
        if k: r.update(k=int(k), m=int(mm), f=int(f), a=alpha_data(Qs, n, int(k)))
        out.append(r)
    return out

def random_records():
    best = {}
    for fn in glob.glob(SOLS + '/*.txt'):
        if 'orb' in os.path.basename(fn): continue
        h = open(fn).readline().split(); d, D = int(h[0]), int(h[1]); N = int(h[h.index('N') + 1])
        if (d, D) not in best or N > best[(d, D)]['N']:
            best[(d, D)] = dict(N=N, g=from_header(h), spec=' '.join(h[2:h.index('N')]), src=os.path.basename(fn))
    return best

def mu_gen(d, D, N): return N * math.exp(-W(d, D) / N)

def old_evals():
    """evals of the random-S run that produced each record (RESULT lines in frontier/runs, wave3, wave4), by (d, D, N)."""
    out = {}
    for fn in glob.glob(os.path.join(HERE, '..', '..', 'frontier', '*', '**', '*'), recursive=True):
        if not os.path.isfile(fn): continue
        for line in open(fn, errors='replace'):
            m = RX.search(line) if line.startswith('RESULT') else None
            if m and m.group(5) == '0':
                key = (int(m.group(1)), int(m.group(2)), int(m.group(4)))
                out[key] = min(out.get(key, 10 ** 12), int(m.group(6)))
    return out

def solve_N(f, target, lo, hi):
    """largest N in [lo, hi] with f(N) <= target (f increasing in N)."""
    for _ in range(200):
        mid = math.sqrt(lo * hi)
        if f(mid) <= target: lo = mid
        else: hi = mid
    return lo

def cap_rule(mu):           # SIZE_LAW §4.1, random-S annealing at (7,8): evals ~ 1e5 exp((mu - 13)/2)
    return 1e5 * math.exp((mu - 13) / 2)

def mu_of_evals(M): return 13 + 2 * math.log(M / 1e5)

def at_N(r, N):
    """the run's group invariants with the order replaced by N (special-target counts held fixed)."""
    return dict(r['g'], order=N)

if __name__ == '__main__':
    runs = load_runs('orb_runs.txt'); cmp = load_runs('cmp_runs.txt'); rec = random_records()
    for r in runs + cmp:
        d, D, N = r['d'], r['D'], r['N']
        r['mu'] = mu_gen(d, D, N); r['mu_m'] = mu_rand(d, D, N, r['g'])
        if r['orbit']:
            r['mua_g'] = mu_orbit(d, D, N, None if D % 2 == 0 else r['g'], r['a'], coincid=False)
            r['mua_m'] = mu_orbit(d, D, N, r['g'], r['a'])

    print('== 1. every orbit run: mu (random S) against the clumped mean mu_alpha (k = 3) ==')
    print('  mu = N e^-lambda; mu_m = model.py (special targets, junction swaps); mu_a = clumped mean, generic / model;')
    print('  evals_pred = random-S capability rule 1e5 exp((x - 13)/2) applied to x = mu_a (generic), no free parameter.')
    print(' cell     group                         N           lam    mu     mu_m   mu_a  mu_a_m  fixed-part  best   evals    evals_pred')
    for r in sorted(runs, key=lambda r: (r['D'], r['d'], r['N'])):
        tot, parts = mu_orbit(r['d'], r['D'], r['N'], r['g'], r['a'], parts=True)
        fx = sum(v for k_, v in parts.items() if k_.endswith('_fixed'))
        print(' (%2d,%2d)  %-28s %11d  %5.2f  %5.1f  %5.1f  %5.1f  %5.1f   %5.2f     %4d  %8d  %9.2g' % (
            r['d'], r['D'], r['spec'][:28], r['N'], lam(r['d'], r['D'], r['N']), r['mu'], r['mu_m'], r['mua_g'], r['mua_m'], fx,
            r['best'], r['evals'], cap_rule(r['mua_g'])))

    print('\n== 2. does the annealer see mu_alpha the way it sees mu? (search-effort law) ==')
    sol = [r for r in runs if r['best'] == 0 and r['evals'] >= 300]
    x = np.array([r['mua_g'] for r in sol]); y = np.log([r['evals'] for r in sol])
    A = np.vstack([np.ones_like(x), x]).T; c, *_ = np.linalg.lstsq(A, y, rcond=None); e = y - A @ c; sd = e.std(ddof=2)
    se = np.sqrt(np.diag(sd ** 2 * np.linalg.inv(A.T @ A)))
    print('  solved orbit runs with >= 300 evals: %d. Fit ln(evals) = a + b mu_alpha: a = %.2f, b = %.3f (se %.3f), resid sd %.2f' % (
        len(sol), c[0], c[1], se[1], sd))
    print('  random-S rule has b = 0.5 and a = ln(1e5) - 6.5 = %.2f.' % (math.log(1e5) - 6.5))
    res = y - np.log([cap_rule(v) for v in x])
    print('  solved runs, ln(evals / rule(mu_alpha)): mean %+.2f, sd %.2f  (rule predicts 0)' % (res.mean(), res.std()))
    x2 = np.array([r['mua_m'] for r in sol]); res2 = y - np.log([cap_rule(v) for v in x2])
    print('  same with the model mu_alpha (special targets, junction swaps): mean %+.2f, sd %.2f' % (res2.mean(), res2.std()))
    xr = np.array([r['mu'] for r in sol]); res3 = y - np.log([cap_rule(v) for v in xr])
    print('  for contrast, the rule applied to plain mu (no clumping): mean %+.2f, sd %.2f' % (res3.mean(), res3.std()))
    uns = [r for r in runs if r['best'] > 0]
    print('  unsolved runs: %d; of these, %d used fewer evals than the rule says mu_alpha needs (consistent), %d used more:' % (
        len(uns), sum(r['evals'] < cap_rule(r['mua_g']) for r in uns), sum(r['evals'] >= cap_rule(r['mua_g']) for r in uns)))
    for r in sorted(uns, key=lambda r: r['evals'] / cap_rule(r['mua_g'])):
        print('     (%2d,%2d) %-30s mu %5.1f  mu_a %5.1f  best %3d  evals %.2g  rule %.2g' % (
            r['d'], r['D'], r['spec'][:30], r['mu'], r['mua_g'], r['best'], r['evals'], cap_rule(r['mua_g'])))

    print('\n  head-to-head (same group, seed, 60 s), random S vs orbit:')
    for r in cmp:
        tag = 'orbit ' if r['orbit'] else 'random'
        xx = r['mua_g'] if r['orbit'] else r['mu']
        print('     %s (%d,%d) %-16s mu %5.1f  effective %5.1f  best %2d  evals %.2g  rule(effective) %.2g' % (
            tag, r['d'], r['D'], r['spec'][:16], r['mu'], xx, r['best'], r['evals'], cap_rule(xx)))

    print('\n== 3. predicted gain per cell ==')
    print('  N_old: best random-S record (frontier/sols, non-orb files); N_new: best solved orbit run.')
    print('  P0 = closed form, clumping only: ln(N_new/N_old) = ln 3 / (1 + lambda_old).')
    print('  P1 = equal difficulty: mu_alpha,model(N_new) = mu_model(N_old), with the new group\'s fixed-point counts.')
    print('  P3 = equal difficulty corrected for budget: mu_alpha(N_new) = mu(N_old) + 2 ln(M_new / M_old), M = evals of the')
    print('       record run (old: frontier run logs; only where the log is in the repo). Generic mu on both sides.')
    oe = old_evals(); cells = {}
    for r in runs:
        if r['best'] == 0 and ((r['d'], r['D']) not in cells or r['N'] > cells[(r['d'], r['D'])]['N']): cells[(r['d'], r['D'])] = r
    rows = []
    print(' cell     N_old        mu_old  lam_old  N_new        gain    P0      P1      P3      M_old    M_new   group (new)')
    for (d, D), r in sorted(cells.items(), key=lambda t: (t[0][1], t[0][0])):
        o = rec[(d, D)]
        if o['N'] >= r['N']: continue
        mo = mu_rand(d, D, o['N'], o['g']); lo = lam(d, D, o['N'])
        g_actual = math.log(r['N'] / o['N'])
        p0 = math.log(3) / (1 + lo)
        f1 = lambda Nx: mu_orbit(d, D, Nx, at_N(r, Nx), r['a'])
        p1 = math.log(solve_N(f1, mo, o['N'] * 0.5, o['N'] * 2) / o['N'])
        Mo = oe.get((d, D, o['N']))
        if Mo:
            f3 = lambda Nx: mu_orbit(d, D, Nx, None if D % 2 == 0 else at_N(r, Nx), r['a'], coincid=False)
            tgt = mu_gen(d, D, o['N']) + 2 * math.log(r['evals'] / Mo)
            p3 = math.log(solve_N(f3, tgt, o['N'] * 0.5, o['N'] * 2) / o['N'])
        else: p3 = float('nan')
        rows.append((d, D, g_actual, p0, p1, p3, r['evals']))
        print(' (%2d,%2d)  %-11d  %6.1f  %5.2f    %-11d  %+5.1f%%  %+5.1f%%  %+5.1f%%  %s  %8s  %7d  %s' % (
            d, D, o['N'], mo, lo, r['N'], 100 * g_actual, 100 * p0, 100 * p1,
            '%+5.1f%%' % (100 * p3) if p3 == p3 else '    - ', Mo or '-', r['evals'], r['spec']))
    a = np.array([t[2:6] for t in rows])
    for j, lab in ((1, 'P0'), (2, 'P1'), (3, 'P3')):
        ok = ~np.isnan(a[:, j]); dif = a[ok, 0] - a[ok, j]
        print('  %s (%2d cells): actual - predicted gain: mean %+.1f%%, rms %.1f%%, corr(actual, pred) %.2f' % (
            lab, ok.sum(), 100 * dif.mean(), 100 * math.sqrt((dif ** 2).mean()), np.corrcoef(a[ok, 0], a[ok, j])[0, 1]))
    ok = ~np.isnan(a[:, 3])
    print('  same %d cells, P1: mean %+.1f%%, rms %.1f%%' % (ok.sum(), 100 * (a[ok, 0] - a[ok, 2]).mean(), 100 * math.sqrt(((a[ok, 0] - a[ok, 2]) ** 2).mean())))
    print('  mean gain: actual %+.1f%%, P0 %+.1f%%, P1 %+.1f%%' % (100 * a[:, 0].mean(), 100 * a[:, 1].mean(), 100 * a[:, 2].mean()))
