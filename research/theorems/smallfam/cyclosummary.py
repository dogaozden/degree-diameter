"""Summary of cyclobound.py scans: how much of the 'index > 6 never solves' pattern is a theorem.
Reads runs/cyclobound_d3D{7,8,9,10}.txt; prints, per index class, groups / solving / rigorously excluded / open, and
the solve rate among the groups the bound leaves open.  Usage: python3 cyclosummary.py FILE..."""
import sys
from collections import defaultdict
rows = []
for fn in sys.argv[1:]:
    D = fn.split('D')[-1].split('.')[0]
    for line in open(fn):
        f = line.split()
        if len(f) < 8:
            continue
        p, k, r, o, N = map(int, f[:5])
        idx = int(f[5].split('=')[1]); sol = int(f[6].split('=')[1]); b = int(f[7].split('=')[1])
        rows.append((D, p, k, o, N, idx, sol, b, f[8]))
def cls(c):
    return '1' if c == 1 else '2' if c == 2 else '3..6' if c <= 6 else '>6'
tab = defaultdict(lambda: [0, 0, 0, 0, 0])
for (D, p, k, o, N, idx, sol, b, st) in rows:
    t = tab[cls(idx)]
    t[0] += 1; t[1] += sol > 0; t[2] += st == 'EXCLUDED'; t[3] += st == 'open'; t[4] += (st == 'open' and sol > 0)
    assert not (st == 'EXCLUDED' and sol > 0), ('bound violated', D, p, k, o)
print('index   groups  solving  excluded_by_bound  open  solving_among_open  rate_among_open')
for c in ['1', '2', '3..6', '>6']:
    g, s, e, op, so = tab[c]
    print(f'{c:6s} {g:7d} {s:8d} {e:18d} {op:5d} {so:19d}  {100.0 * so / op if op else 0:.1f} %')
tot = [sum(tab[c][i] for c in tab) for i in range(5)]
print(f'all    {tot[0]:7d} {tot[1]:8d} {tot[2]:18d} {tot[3]:5d} {tot[4]:19d}  {100.0 * tot[4] / tot[3]:.1f} %')
# the open index > 6 groups: what are they?
op6 = [(D, p, k, o, N, b) for (D, p, k, o, N, idx, sol, b, st) in rows if st == 'open' and idx > 6]
print(f'\nopen groups with index > 6: {len(op6)}; by action order o:',
      dict(sorted(defaultdict(int, {o: sum(1 for x in op6 if x[3] == o) for o in set(x[3] for x in op6)}).items())))
