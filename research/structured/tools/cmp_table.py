"""Markdown table from cmp.sh output: one row per (cell, group), one column per variant (same seeds and budget).
usage: python3 cmp_table.py LOG"""
import sys, re, math
from collections import defaultdict
def W(d, D):
    if D % 2: k = (D - 1) // 2; return 1 + sum(d * (d - 1) ** (2 * i - 1) for i in range(1, k + 1))
    k = D // 2; return d * sum((d - 1) ** (2 * i) for i in range(k))
rows = defaultdict(lambda: defaultdict(list)); kinds = []
for line in open(sys.argv[1]):
    m = re.match(r'(\S+) .*seed (\d+) :: RESULT d=(\d+) D=(\d+) group=(.+?) N=(\d+) best=(\d+) evals=(\d+)', line)
    if not m: continue
    kind, seed, d, D, grp, N, best, ev = m.groups()
    if kind == 'orbit3': kind = '3,2,1'          # old cmp.sh label
    if kind not in kinds: kinds.append(kind)
    rows[(int(d), int(D), grp.strip(), int(N))][kind].append((int(seed), int(best), int(ev)))
lab = lambda k: 'random S' if k == 'random' else 'orbit (k,m,f)=(%s)' % k.replace(',', ', ', 2)
print('| cell | group | N | μ | ' + ' | '.join(lab(k) + ': solved, evals (or best cost)' for k in kinds) + ' |')
print('|---|---|---|---|' + '---|' * len(kinds))
f = lambda L: '%d/%d; %s' % (sum(b == 0 for _, b, _ in L), len(L), ', '.join(('%.3g' % e if b == 0 else 'best %d @ %.2g' % (b, e)) for _, b, e in sorted(L))) if L else '—'
for (d, D, grp, N), v in rows.items():
    mu = N * math.exp(-W(d, D) / N)
    print('| (%d,%d) | %s | %s | %.1f | %s |' % (d, D, grp, format(N, ','), mu, ' | '.join(f(v[k]) for k in kinds)))
