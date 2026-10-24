"""Summarise the c6 runs: E18 per group = median over seeds of (evals if solved else 3*evals) * exp((18 - mu)/4.5)."""
import glob, math, os, re, statistics, sys
L = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'logs')
groups = {}
for out in sorted(glob.glob(os.path.join(L, '*.out'))):
    tag = os.path.basename(out)[:-4]
    grp, seed = tag.rsplit('_s', 1)
    txt = open(out).read()
    err = open(out[:-4] + '.err').read()
    m = re.search(r'RESULT d=16 D=8 group=(\S.*?) x Z_(\d+) N=(\d+) best=(-?\d+) evals=(\d+) time=([\d.]+)', txt)
    mu = re.search(r'mu = ([\d.]+)', err)
    if not m:
        print('%-22s seed %s: no RESULT (incomplete or failed)' % (grp, seed)); continue
    best, evals, secs, N = int(m.group(4)), int(m.group(5)), float(m.group(6)), int(m.group(3))
    mu = float(mu.group(1)) if mu else float('nan')
    fix = re.search(r'Fix\(alpha\)\| = (\d+)', err)
    groups.setdefault(grp, {'mu': mu, 'N': N, 'fix': fix.group(1) if fix else '?', 'runs': []})['runs'].append((int(seed), best, evals, secs))
rows = []
for grp, g in groups.items():
    vals = [(e if b == 0 else 3 * e) for (_, b, e, _) in g['runs']]
    med = statistics.median(vals)
    e18 = med * math.exp((18 - g['mu']) / 4.5)
    rows.append((e18, grp, g))
print('%-22s %9s %6s %5s  %s' % ('group', 'N', 'mu', 'fix', 'runs (seed: best evals time)'))
for e18, grp, g in sorted(rows):
    runs = '; '.join('s%d: best=%d evals=%d t=%.1f' % r for r in sorted(g['runs']))
    print('%-22s %9d %6.2f %5s  %s' % (grp, g['N'], g['mu'], g['fix'], runs))
    print('%-22s median_evals=%.0f  E18=%.0f  (solved %d/%d)' % ('', statistics.median([(e if b == 0 else 3 * e) for (_, b, e, _) in g['runs']]), e18,
          sum(1 for r in g['runs'] if r[1] == 0), len(g['runs'])))
print('reference sl 53 x Z91 (preamble, seed 1, same 90 s budget): evals=3017 mu=18.25 E18=%.0f' % (3017 * math.exp((18 - 18.25) / 4.5)))
