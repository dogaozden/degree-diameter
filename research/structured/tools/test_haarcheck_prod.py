"""Self-test of haarcheck_prod against a brute-force diameter on small random product Haar graphs."""
import random, subprocess, os, sys, itertools
from collections import deque
import haarcheck_prod as h

def brute(FA, FB, n, gens, D):
    EA = h.sl_elements(FA); EB = h.sl_elements(FB)
    verts = [(x, y, z, s) for s in (0, 1) for x in EA for y in EB for z in range(n)]
    idx = {v: i for i, v in enumerate(verts)}
    adj = [[] for _ in verts]
    for (x, y, z, s) in verts:
        for (ga, gb, zz) in gens:
            if s == 0:  # (g,A) ~ (s g, B)
                nb = (h.mat_mul(FA, ga, x), h.mat_mul(FB, gb, y), (zz + z) % n, 1)
                adj[idx[(x, y, z, s)]].append(idx[nb])
    for (x, y, z, s) in verts:
        if s == 1:
            for (ga, gb, zz) in gens:
                nb = (h.mat_mul(FA, h.mat_inv(FA, ga), x), h.mat_mul(FB, h.mat_inv(FB, gb), y), (z - zz) % n, 0)
                adj[idx[(x, y, z, s)]].append(idx[nb])
    ecc = 0
    for src in [idx[((1, 0, 0, 1), (1, 0, 0, 1), 0, s)] for s in (0, 1)]:
        dist = [-1] * len(verts); dist[src] = 0; dq = deque([src])
        while dq:
            v = dq.popleft()
            for u in adj[v]:
                if dist[u] < 0: dist[u] = dist[v] + 1; dq.append(u)
        if min(dist) < 0: return None
        ecc = max(ecc, max(dist))
    return ecc

def run(FA, FB, n, gens, D, tmpdir):
    EA = h.sl_elements(FA); EB = h.sl_elements(FB)
    IA = {x: t for t, x in enumerate(EA)}; IB = {x: t for t, x in enumerate(EB)}
    out = ['%d %d %d %d %d' % (len(EA), len(EB), n, len(gens), D)]
    for ga, gb, z in gens:
        out.append(str(z))
        out.append(' '.join(str(IA[h.mat_mul(FA, ga, x)]) for x in EA))
        out.append(' '.join(str(IA[h.mat_mul(FA, h.mat_inv(FA, ga), x)]) for x in EA))
        out.append(' '.join(str(IB[h.mat_mul(FB, gb, y)]) for y in EB))
        out.append(' '.join(str(IB[h.mat_mul(FB, h.mat_inv(FB, gb), y)]) for y in EB))
    out.append('%d %d' % (IA[(1, 0, 0, 1)], IB[(1, 0, 0, 1)]))
    tab = os.path.join(tmpdir, 't.txt'); open(tab, 'w').write('\n'.join(out) + '\n')
    r = subprocess.run([os.path.join(os.path.dirname(os.path.abspath(__file__)), 'haarcheck_prod'), tab], capture_output=True, text=True)
    return r.stdout

random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
tmp = os.environ.get('TMPDIR', '.')
bad = 0; checked = 0
for trial in range(40):
    FA = h.GF(random.choice([2, 3, 4, 5])); FB = h.GF(random.choice([2, 3, 4, 5]))
    n = random.choice([1, 2, 3, 5])
    EA = h.sl_elements(FA); EB = h.sl_elements(FB)
    d = random.randint(3, 5)
    gens = set()
    while len(gens) < d:
        gens.add((random.choice(EA), random.choice(EB), random.randrange(n)))
    gens = sorted(gens)
    if (1, 0, 0, 1) not in [g[0] for g in gens] and False: pass
    D = random.randint(2, 4)
    truth = brute(FA, FB, n, gens, D)
    got = run(FA, FB, n, gens, D, tmp)
    # parse the checker's ecc values
    import re
    m = re.search(r'ecc\(e,A\)=(\d+) ecc\(e,B\)=(\d+)', got)
    cnt = re.search(r'reached A=(\d+) B=(\d+) of (\d+)', got)
    should_be_valid = truth is not None and truth <= D
    if not should_be_valid:
        ok = 'INVALID' in got
    else:
        ok = 'VALID' in got and 'INVALID' not in got and m is not None and max(int(m.group(1)), int(m.group(2))) == truth
    checked += 1
    if not ok:
        bad += 1; print('MISMATCH trial', trial, 'brute', truth, 'got', got.strip().replace('\n', ' | '))
print('checked', checked, 'mismatches', bad)
