"""Collect every haar_sym run of this session: cell, group, N, 2N, mu, structure, result, evaluations, seconds."""
import glob, re, os, math
here = os.path.dirname(os.path.abspath(__file__))
W = lambda d, D: 1 + sum(d * (d - 1) ** (2 * i - 1) for i in range(1, (D - 1) // 2 + 1))
rows = []
for f in sorted(glob.glob(os.path.join(here, 'solo_runs', '*.log'))):
    s = open(f).read()
    m = re.search(r'RESULT d=(\d+) D=(\d+) group=(.*?) N=(\d+) best=(\d+) evals=(\d+) time=([\d.]+) orbit k=(\d+) m=(\d+) f=(\d+) fix=(\d+)', s)
    if not m:
        t = re.findall(r't=(\d+) steps=\d+ evals=(\d+) cost=\d+ best=(\d+)', s)
        tag = os.path.basename(f)[:-4]
        if t: rows.append((tag, 'running/stopped: best %s after %s evals, %s s' % (t[-1][2], t[-1][1], t[-1][0])))
        continue
    d, D, grp, N, best, ev, tm, k, mm, ff, fix = m.groups()
    d, D, N = int(d), int(D), int(N)
    mu = N * math.exp(-W(d, D) / N)
    valid = 'VALID' if re.search(r'^VALID d=', s, re.M) else ''
    rows.append((d, D, grp.replace(' poly x^3+x+1', '').replace(' poly x^2+x+1', ''), N, 2 * N, mu, '%s,%s,%s' % (k, mm, ff), fix, int(best), int(ev), float(tm), valid, os.path.basename(f)))
print('| cell | group | N | 2N | mu | k,m,f | Fix | best cost | evals | s | build_haar2 |')
print('|---|---|---|---|---|---|---|---|---|---|---|')
for r in sorted([r for r in rows if len(r) > 2], key=lambda r: (r[0], r[3])):
    print('| (%d,%d) | %s | %d | %d | %.1f | %s | %s | %d | %.1e | %.0f | %s |' % (r[0], r[1], r[2], r[3], r[4], r[5], r[6], r[7], r[8], r[9], r[10], r[11]))
for r in rows:
    if len(r) == 2: print('#', r[0], r[1])
