"""Markdown table from cmp.sh output (random-S vs orbit annealing, same groups/seeds/budget)."""
import sys, re, math
from collections import defaultdict
def W(d, D):
    if D % 2: k = (D - 1) // 2; return 1 + sum(d * (d - 1) ** (2 * i - 1) for i in range(1, k + 1))
    k = D // 2; return d * sum((d - 1) ** (2 * i) for i in range(k))
rows = defaultdict(lambda: {'random': [], 'orbit': []})
for line in open(sys.argv[1]):
    m = re.match(r'(random|orbit).*seed (\d+) :: RESULT d=(\d+) D=(\d+) group=(.+?) N=(\d+) best=(\d+) evals=(\d+)', line)
    if not m: continue
    kind, seed, d, D, grp, N, best, ev = m.groups()
    key = (int(d), int(D), grp.strip(), int(N))
    rows[key][kind].append((int(seed), int(best), int(ev)))
print('| cell | group | N | μ | random S: solved, evals (or best cost) | orbit k=3: solved, evals |')
print('|---|---|---|---|---|---|')
for (d, D, grp, N), v in rows.items():
    mu = N * math.exp(-W(d, D) / N)
    f = lambda L: '%d/%d; %s' % (sum(b == 0 for _, b, _ in L), len(L), ', '.join(('%.3g' % e if b == 0 else 'best %d @ %.2g' % (b, e)) for _, b, e in sorted(L)))
    print('| (%d,%d) | %s | %s | %.1f | %s | %s |' % (d, D, grp, format(N, ','), mu, f(v['random']), f(v['orbit'])))
