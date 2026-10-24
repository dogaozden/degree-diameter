"""Permutation test, within each cell: do solved runs differ from stalled runs in fail_Q, excess_Q or mu?
Statistic: difference of means (solved - stalled), pooled over cells after centring each feature within its cell;
p-value from 20000 within-cell label permutations.  Input: runs/predict_out.txt.  Output: runs/predict_test_out.txt."""
import random
rows = []
for l in open('runs/predict_out.txt'):
    p = l.split('|')
    if len(p) != 4 or not p[0].strip()[0].isdigit():
        continue
    D, Dd, N = p[0].split()[:3]
    best = int(p[1]); mu = float(p[2]); fq, ex = map(float, p[3].split())
    rows.append(((int(D), int(Dd)), best == 0, fq, ex, mu))
cells = {}
for r in rows:
    cells.setdefault(r[0], []).append(r)
cells = {c: L for c, L in cells.items() if any(x[1] for x in L) and not all(x[1] for x in L)}
out = []
for fi, name in ((2, 'fail_Q'), (3, 'excess_Q'), (4, 'mu')):
    def stat(labels):
        s, n = 0.0, 0
        for c, L in cells.items():
            vals = [x[fi] for x in L]
            m = sum(vals) / len(vals)
            lab = labels[c]
            sv = [v - m for v, y in zip(vals, lab) if y]
            st = [v - m for v, y in zip(vals, lab) if not y]
            s += (sum(sv) / len(sv) - sum(st) / len(st)) * len(L); n += len(L)
        return s / n
    obs = stat({c: [x[1] for x in L] for c, L in cells.items()})
    random.seed(3); cnt = 0; R = 20000
    for _ in range(R):
        perm = {}
        for c, L in cells.items():
            lab = [x[1] for x in L]; random.shuffle(lab); perm[c] = lab
        if abs(stat(perm)) >= abs(obs): cnt += 1
    out.append(f'{name}: within-cell mean difference solved - stalled = {obs:+.4f}, two-sided permutation p = {cnt / R:.3f} '
               f'(cells with both outcomes: {sorted(cells)}; runs {sum(len(L) for L in cells.values())})')
open('runs/predict_test_out.txt', 'w').write('\n'.join(out) + '\n')
print('\n'.join(out))
