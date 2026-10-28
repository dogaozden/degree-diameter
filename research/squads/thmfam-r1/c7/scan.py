"""c7 scanner: for p, q, list of m, try label choices, print best (component size, diam) per m as JSON lines."""
import sys, subprocess, re, json, random, math
sys.path.insert(0, '/home/user/degree-diameter/research/squads/thmfam-r1/c7')
import c7lib
from c7lib import parse, orbits, labels, root3
HE = '/home/user/degree-diameter/research/theorems/haar_families/haar_ecc'
_cache = {}
def base(p, q):
    if (p, q) not in _cache:
        g = parse(p, q); perm, cyc = orbits(g); _cache[(p, q)] = (g, cyc)
    return _cache[(p, q)]
def run(p, q, m, ts):
    g, cyc = base(p, q)
    z = labels(g, cyc, m, ts)
    txt = ''.join('%d %d %d %d %d\n' % (*g[i][1], z[i]) for i in range(len(g)))
    r = subprocess.run([HE, 'pgl', str(q), str(m)], input=txt, capture_output=True, text=True, timeout=900)
    mm = re.search(r'compA=(\d+) compB=(\d+) order=(\d+) connected=(\w+) diam=(\d+)', r.stdout)
    if not mm: return None
    cA, cB, order, conn, diam = int(mm.group(1)), int(mm.group(2)), int(mm.group(3)), mm.group(4), int(mm.group(5))
    if cA != cB: return None
    return cA, diam
def valid_m(m):
    if m == 1: return True
    try:
        r = root3(m)
    except ValueError:
        return False
    return math.gcd(r - 1, m) == 1
if __name__ == '__main__':
    p = int(sys.argv[1]); q = int(sys.argv[2])
    ms = [int(x) for x in sys.argv[3].split(',')]
    K = int(sys.argv[4]) if len(sys.argv) > 4 else 8
    g, cyc = base(p, q)
    n3 = sum(1 for c in cyc if len(c) == 3)
    random.seed(1)
    for m in ms:
        if not valid_m(m): continue
        best = None
        cands = list(range(m)) if m <= K else random.sample(range(m), K)
        if n3 == 2:
            tsets = [(1, t) for t in cands]
        else:
            tsets = [tuple([1] + random.sample(range(m), n3 - 1)) for _ in range(K)] if m > 1 else [(1,) * n3]
        for ts in tsets:
            res = run(p, q, m, list(ts))
            if res is None: continue
            n, diam = res
            if best is None or diam < best[1] or (diam == best[1] and n > best[0]): best = (n, diam, ts)
        if best: print(json.dumps({'p': p, 'q': q, 'm': m, 'n': best[0], 'diam': best[1], 'ts': best[2]}), flush=True)
