"""Rank screened groups: python3 rank.py screen_file [top] . Score = (p1+p10)/2 / mu (lower is better)."""
import sys
f = sys.argv[1]; top = int(sys.argv[2]) if len(sys.argv) > 2 else 30
rows = []
for line in open(f):
    x = line.rstrip('\n').split('\t')
    if len(x) < 11 or x[10] != 'ok': continue
    N, fam, spec, mu = int(x[0]), x[1], x[2], float(x[3])
    fix, mn, p1, p10, med, secs = int(x[4]), int(x[5]), int(x[6]), int(x[7]), int(x[8]), float(x[9])
    rows.append(((p1 + p10) / 2 / mu, p1 / mu, med / mu, N, mu, fix, mn, p1, p10, med, spec, secs))
rows.sort()
print('rank  score(p1p10/mu)  p1/mu  med/mu  N  mu  fix  min  p1  p10  median  spec  secs')
for i, r in enumerate(rows[:top]):
    print('%3d  %.3f  %.3f  %.2f  %d  %.1f  %d  %d  %d  %d  %d  %s  %.1f' % ((i + 1,) + r[:2] + (r[2],) + r[3:]))
print('screened: %d ok of %d lines' % (len(rows), sum(1 for _ in open(f))))
