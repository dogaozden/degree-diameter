# card c3: E18 per base-group type (SL / PGL / PSL) from logs/*.out, logs/*.err, logs/*.rc
# E18 = median over seeds of (evals if solved else 3*evals) * exp((18 - mu)/4.5)
import math, os, re, statistics, sys
HERE = os.path.dirname(os.path.abspath(__file__))
LOG = os.path.join(HERE, 'logs')
jobs = [l.split() for l in open(os.path.join(HERE, 'jobs.txt')) if l.strip()]
rows = []
for tag, seed, secs, typ, p, n in jobs:
    out = open(os.path.join(LOG, tag + '.out')).read() if os.path.exists(os.path.join(LOG, tag + '.out')) else ''
    err = open(os.path.join(LOG, tag + '.err')).read() if os.path.exists(os.path.join(LOG, tag + '.err')) else ''
    rc = open(os.path.join(LOG, tag + '.rc')).read().strip() if os.path.exists(os.path.join(LOG, tag + '.rc')) else 'missing'
    m = re.search(r'RESULT .* N=(\d+) best=(\d+) evals=(\d+) time=([\d.]+) orbit k=3 m=5 f=1 fix=(\d+)', out)
    mu_m = re.search(r'mu = ([\d.]+)', err)
    if not m or not mu_m:
        rows.append(dict(tag=tag, typ=typ, p=p, n=n, ok=False, rc=rc)); continue
    N, best, evals, t, fix = int(m.group(1)), int(m.group(2)), int(m.group(3)), float(m.group(4)), int(m.group(5))
    mu = float(mu_m.group(1))
    solved = best == 0
    check = 'OK' if 'full diameter check: OK' in out else ('FAIL' if 'full diameter check: FAIL' in out else 'n/a')
    rows.append(dict(tag=tag, typ=typ, p=p, n=n, ok=True, rc=rc, N=N, best=best, evals=evals, time=t, fix=fix,
                     mu=mu, solved=solved, check=check, cost=evals if solved else 3 * evals, seed=seed))
print('%-14s %-4s %-3s %-4s %10s %5s %6s %9s %8s %7s %6s %s' % ('tag', 'type', 'p', 'n', 'N', 'mu', 'best', 'evals', 'time', 'fix', 'check', 'rc'))
for r in rows:
    if not r['ok']:
        print('%-14s %-4s %-3s %-4s  (no RESULT; rc=%s)' % (r['tag'], r['typ'], r['p'], r['n'], r['rc'])); continue
    print('%-14s %-4s %-3s %-4s %10d %5.2f %6d %9d %8.1f %7d %6s %s' % (r['tag'], r['typ'], r['p'], r['n'], r['N'], r['mu'],
          r['best'], r['evals'], r['time'], r['fix'], r['check'], r['rc']))
print()
types = {}
for r in rows:
    if r['ok']: types.setdefault(r['typ'], []).append(r)
res = []
for typ, rs in types.items():
    mu = rs[0]['mu']
    med = statistics.median([r['cost'] for r in rs])
    e18 = med * math.exp((18 - mu) / 4.5)
    solved = sum(r['solved'] for r in rs)
    res.append((e18, typ, rs[0]['p'], rs[0]['n'], mu, med, solved, len(rs), sorted(r['evals'] for r in rs)))
res.sort()
print('%-5s %-6s %-4s %-4s %6s %12s %10s %s' % ('rank', 'type', 'p', 'n', 'mu', 'median_cost', 'E18', 'solved/seeds (evals of each seed)'))
for i, (e18, typ, p, n, mu, med, solved, tot, ev) in enumerate(res):
    print('%-5d %-6s %-4s %-4s %6.2f %12.0f %10.0f %d/%d %s' % (i + 1, typ, p, n, mu, med, e18, solved, tot, ev))
if res:
    best = res[0]
    print('\nBEST E18 = %.0f (type %s, p=%s, n=%s, mu=%.2f)' % (best[0], best[1], best[2], best[3], best[4]))
