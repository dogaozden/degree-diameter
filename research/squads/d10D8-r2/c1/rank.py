"""Effective-mu ranking from zdup_raw.txt (haar_zopt ZONLYDUP, ZOPT=r:3). Writes results.tsv (data table, not a report).
effective mu = mu_nominal * exp(delta * lambda), lambda = 5380840 / N, delta = mean duplicate fraction over the 3 random sets."""
import re, math
W = 5380840                                   # words of length <= D-1 for d=10, D=8 (binding-word count, Wwords)
blocks, cur = [], None
for line in open('zdup_raw.txt'):
    line = line.rstrip('\n')
    m = re.match(r'## N=(\d+) mu=([\d.]+) spec=\[(.*)\]', line)
    if m:
        cur = {'N': int(m.group(1)), 'mu': float(m.group(2)), 'spec': m.group(3), 'dup': [], 'coef': None, 'fix': None, 'rc': None}
        blocks.append(cur); continue
    if cur is None: continue
    m = re.search(r'ZCOEF .* \(([\d.]+) % of words\)', line)
    if m: cur['coef'] = float(m.group(1))
    m = re.search(r'ZDUP rep (\d+): words (\d+) distinct \(q,c\) (\d+) duplicate (\d+) \(([\d.]+) %\)', line)
    if m:
        assert int(m.group(2)) == W, line
        cur['dup'].append(float(m.group(5)))
    m = re.search(r'\|Fix\(alpha\)\| = (\d+)', line)
    if m: cur['fix'] = int(m.group(1))
    if 'error' in line.lower() or 'needs' in line: cur.setdefault('err', []).append(line)
rows = []
for b in blocks:
    N = b['N']; lam = W / N
    d = [x / 100 for x in b['dup']]
    delta = sum(d) / len(d)
    mu = N * math.exp(-lam)                    # nominal mu, recomputed from N (check against list)
    mu_eff = b['mu'] * math.exp(delta * lam)
    rows.append((mu_eff, b, delta, lam))
rows.sort(key=lambda r: r[0])
with open('results.tsv', 'w') as f:
    f.write('rank\tN\t2N\tn\tspec\tmu_nominal\tlambda\tfix_alpha\tdup_rep0\tdup_rep1\tdup_rep2\tdelta_mean\tcoef_generic_pct\tmu_effective\n')
    for i, (me, b, delta, lam) in enumerate(rows, 1):
        n = b['spec'].split()[-1]
        d = b['dup']
        f.write('%d\t%d\t%d\t%s\t%s\t%.2f\t%.3f\t%s\t%.2f\t%.2f\t%.2f\t%.4f\t%s\t%.1f\n' % (
            i, b['N'], 2 * b['N'], n, b['spec'], b['mu'], lam, b['fix'], d[0], d[1], d[2], delta,
            b['coef'], me))
for i, (me, b, delta, lam) in enumerate(rows[:12], 1):
    print('%2d N=%d n=%s mu=%.1f delta=%.3f eff_mu=%.1f  %s' % (i, b['N'], b['spec'].split()[-1], b['mu'], delta, me, b['spec']))
print('...')
for i, (me, b, delta, lam) in enumerate(rows, 1):
    if b['spec'] == 'psl 23 97': print('psl 23 97 rank %d of %d: mu=%.1f delta=%.3f eff_mu=%.1f' % (i, len(rows), b['mu'], delta, me))
print('groups', len(rows), 'errors', [b.get('err') for b in blocks if b.get('err')])
