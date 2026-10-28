"""c7: largest valid m (component n = |PGL| m) with diam <= D over K label choices. Usage: bis.py p q D [K]"""
import sys, json, random
sys.path.insert(0, '/home/user/degree-diameter/research/squads/thmfam-r1/c7')
from scan import run, base, valid_m
p, q, D = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
K = int(sys.argv[4]) if len(sys.argv) > 4 else 6
g, cyc = base(p, q)
n3 = sum(1 for c in cyc if len(c) == 3)
PGL = q * (q * q - 1)
ms = [m for m in range(1, int(3e7 // PGL) + 1) if valid_m(m)]
rng = random.Random(7 * p + q)
cache = {}
def ok(i):
    """index i in ms: best (n, diam, ts) with diam <= D, or None."""
    if i in cache: return cache[i]
    m = ms[i]; best = None
    for k in range(K):
        if m == 1: ts = [0] * n3 if n3 == 2 else [0] * n3
        elif n3 == 2: ts = [1, 0] if k == 0 else [1, rng.randrange(m)]
        else: ts = [1] + [0] * (n3 - 1) if k == 0 else [1] + [rng.randrange(m) for _ in range(n3 - 1)]
        res = run(p, q, m, ts)
        if res is None: continue
        n, diam = res
        if diam <= D:
            best = (n, diam, ts); break
    cache[i] = best
    return best
# geometric scan for a failing index
lo = -1; i = 0
while i < len(ms):
    if ok(i) is None: break
    lo = i
    i = max(i + 1, int(i * 1.5) + 1)
if lo < 0:
    print(json.dumps({'p': p, 'q': q, 'D': D, 'best': None}), flush=True); sys.exit()
hi = min(i, len(ms) - 1) if i < len(ms) else len(ms)
if hi < len(ms) and ok(hi) is not None:
    lo = hi; hi = len(ms)
while hi - lo > 1 and hi < len(ms):
    mid = (lo + hi) // 2
    if ok(mid) is None: hi = mid
    else: lo = mid
b = ok(lo)
print(json.dumps({'p': p, 'q': q, 'D': D, 'm': ms[lo], 'n': b[0], 'diam': b[1], 'ts': b[2], 'PGL': PGL}), flush=True)
