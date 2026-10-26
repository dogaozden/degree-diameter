"""Join effective-mu table (results.tsv) with RANDORB tails (randorb_all_raw.txt, 1000 samples) and report rank correlations."""
import re, csv, math
def avg_ranks(v):
    o = sorted(range(len(v)), key=lambda i: v[i]); r = [0.0] * len(v); i = 0
    while i < len(o):
        j = i
        while j + 1 < len(o) and v[o[j + 1]] == v[o[i]]: j += 1
        for k in range(i, j + 1): r[o[k]] = (i + j) / 2 + 1
        i = j + 1
    return r
def spearman(x, y):
    rx, ry = avg_ranks(x), avg_ranks(y); n = len(x); mx, my = sum(rx) / n, sum(ry) / n
    sxy = sum((a - mx) * (b - my) for a, b in zip(rx, ry)); sxx = sum((a - mx) ** 2 for a in rx); syy = sum((b - my) ** 2 for b in ry)
    return sxy / math.sqrt(sxx * syy)
tail = {}; spec = None
for line in open('randorb_all_raw.txt'):
    m = re.match(r'## N=\d+ spec=\[(.*)\]', line)
    if m: spec = m.group(1); continue
    m = re.match(r'RANDORB d=.* group=(.*) N=(\d+) k=3 m=3 f=1 fix=(\d+) samples=(\d+) min=(\d+) p1=(\d+) p10=(\d+) median=(\d+)', line)
    if m and spec: tail[spec] = dict(fix=int(m.group(3)), smp=int(m.group(4)), min=int(m.group(5)), p1=int(m.group(6)), p10=int(m.group(7)), med=int(m.group(8)))
rows = list(csv.DictReader(open('results.tsv'), delimiter='\t'))
for r in rows:
    t = tail[r['spec']]; r.update({k: t[k] for k in ('min', 'p1', 'p10', 'med', 'smp')}); r['fixrb'] = t['fix']
    r['mu_eff'] = float(r['mu_effective']); r['delta'] = float(r['delta_mean']); r['mu_nom'] = float(r['mu_nominal'])
with open('results_randorb.tsv', 'w') as f:
    cols = ['rank', 'N', 'n', 'spec', 'mu_nominal', 'delta_mean', 'mu_effective', 'fix_alpha', 'min', 'p1', 'p10', 'med', 'smp']
    f.write('\t'.join(cols) + '\n')
    for r in sorted(rows, key=lambda r: r['mu_eff']):
        f.write('\t'.join(str(r[c]) for c in cols) + '\n')
print('groups joined:', len(rows))
x_eff = [r['mu_eff'] for r in rows]; x_nom = [r['mu_nom'] for r in rows]; x_del = [r['delta'] for r in rows]
x_fix = [r['fixrb'] for r in rows]
mins = [r['min'] for r in rows]; p1s = [r['p1'] for r in rows]; p10s = [r['p10'] for r in rows]; meds = [r['med'] for r in rows]
for name, x in [('mu_effective', x_eff), ('mu_nominal', x_nom), ('delta', x_del), ('fix_alpha', x_fix)]:
    print('spearman(%-12s, min)=%+.2f  (p1)=%+.2f  (p10)=%+.2f  (median)=%+.2f' % (name, spearman(x, mins), spearman(x, p1s), spearman(x, p10s), spearman(x, meds)))
rk = {r['spec']: i + 1 for i, r in enumerate(sorted(rows, key=lambda r: r['mu_eff']))}
rp1 = {r['spec']: i + 1 for i, r in enumerate(sorted(rows, key=lambda r: r['p1']))}
rmin = {r['spec']: i + 1 for i, r in enumerate(sorted(rows, key=lambda r: r['min']))}
print('by p1, top 8 (eff-mu rank in brackets):')
for r in sorted(rows, key=lambda r: r['p1'])[:8]: print('  p1=%d min=%d  [eff rank %d, mu_eff %.1f, fix %d]  %s' % (r['p1'], r['min'], rk[r['spec']], r['mu_eff'], r['fixrb'], r['spec']))
print('by min, top 8:')
for r in sorted(rows, key=lambda r: r['min'])[:8]: print('  min=%d p1=%d  [eff rank %d, mu_eff %.1f, fix %d]  %s' % (r['min'], r['p1'], rk[r['spec']], r['mu_eff'], r['fixrb'], r['spec']))
for s in ['psl 23 97', 'pgl 27 31', 'sl 27 31', 'sl 32 19', 'pgl 32 19']:
    r = [q for q in rows if q['spec'] == s][0]
    print('%-10s eff rank %2d/46 (mu_eff %.1f); p1 rank %2d/46 (p1 %d); min rank %2d/46 (min %d); fix %d; med %d' % (s, rk[s], r['mu_eff'], rp1[s], r['p1'], rmin[s], r['min'], r['fixrb'], r['med']))
