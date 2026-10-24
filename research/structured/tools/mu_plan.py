"""Per-cell planning for orbit search: mu = N exp(-W/N) at the table value and at our best, and the orders where mu
reaches given levels.  usage: python3 mu_plan.py [mu1 mu2 ...]   (default 20 45)"""
import sys, math, os, glob, re
here = os.path.dirname(os.path.abspath(__file__))
fr = os.path.join(here, '..', '..', 'frontier')
def W(d, D):
    if D % 2: k = (D - 1) // 2; return 1 + sum(d * (d - 1) ** (2 * i - 1) for i in range(1, k + 1))
    k = D // 2; return d * sum((d - 1) ** (2 * i) for i in range(k))
def mu(d, D, N): return N * math.exp(-W(d, D) / N)
def N_at(d, D, m):          # largest N with mu(N) <= m (mu increasing in N on the relevant range)
    lo, hi = 2.0, float(W(d, D))
    for _ in range(200):
        mid = (lo + hi) / 2
        if mu(d, D, mid) <= m: lo = mid
        else: hi = mid
    return lo
def Nh(d, D):
    w = W(d, D); lo, hi = 10.0, float(w)
    for _ in range(200):
        m = (lo + hi) / 2
        if m * math.exp(-w / m) < d * math.log(m): lo = m
        else: hi = m
    return lo
table = {}; seen = set()
for line in open(os.path.join(fr, 'TABLE.md')):
    m = re.match(r'\|\s*(\d+)\s*\|(.*)\|\s*$', line)
    if not m: continue
    d = int(m.group(1)); cells = m.group(2).split('|')
    if len(cells) != 8 or d in seen: continue
    seen.add(d)
    for D, c in zip(range(3, 11), cells):
        v = re.match(r'\s*([\d,]+)', c)
        if v: table[(d, D)] = int(v.group(1).replace(',', ''))
ours = {}
for f in glob.glob(os.path.join(fr, 'sols', '*.txt')) + glob.glob(os.path.join(here, '..', 'sols', '*.txt')):
    h = open(f).readline().split()
    try: d, D, N = int(h[0]), int(h[1]), int(h[-1])
    except Exception: continue
    ours[(d, D)] = max(ours.get((d, D), 0), 2 * N)
levels = [float(x) for x in sys.argv[1:]] or [20.0, 45.0]
print('cell     table        ours         mu@table mu@ours  ' + '  '.join('2N(mu=%g)' % l for l in levels) + '   2N_h        table/2N_h')
for D in (5, 7, 8, 9, 10):
    for d in range(3, 17):
        t = table.get((d, D)); o = ours.get((d, D))
        if not t: continue
        mt = mu(d, D, t // 2 + 1); mo = mu(d, D, o // 2 + 1) if o else float('nan')
        ns = ['%12d' % (2 * N_at(d, D, l)) for l in levels]
        nh = 2 * Nh(d, D)
        print('(%2d,%2d) %12d %12s %8.1f %8.1f ' % (d, D, t, o or '-', mt, mo) + ' '.join(ns) + ' %12d %6.2f' % (nh, t / nh))
