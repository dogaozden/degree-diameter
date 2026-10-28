"""c7: LPS generators of PGL(2,q) with a cyclic-shift automorphism alpha, and Z_m labels.
gen_c7.py p q m t1 t2 ... prints "a b c d z" lines for haar_ecc pgl q m."""
import subprocess, sys, itertools
LPS = '/home/user/degree-diameter/research/theorems/haar_families/lps_haar'

def parse(p, q):
    out = subprocess.run([LPS, str(p), str(q), '-v'], capture_output=True, text=True, timeout=600).stdout
    gens = []
    for line in out.splitlines():
        if line.startswith('gen '):
            quat = tuple(int(x) for x in line.split('quat (')[1].split(')')[0].split(','))
            mat = tuple(int(x) for x in line.split('mat(')[1].split(')')[0].split(','))
            gens.append((quat, mat))
    return gens

def canon(t):
    neg = tuple(-x for x in t)
    return max(t, neg)

def shift(t):
    a0, a1, a2, a3 = t
    return (a0, a3, a1, a2)

def orbits(gens):
    """alpha-orbits on generator indices: list of cycles (index tuples), fixed points as length-1."""
    idx = {canon(g[0]): i for i, g in enumerate(gens)}
    perm = [idx[canon(shift(g[0]))] for g in gens]
    seen = set(); cyc = []
    for i in range(len(gens)):
        if i in seen: continue
        c = [i]; seen.add(i); j = perm[i]
        while j != i:
            c.append(j); seen.add(j); j = perm[j]
        cyc.append(tuple(c))
    return perm, cyc

def root3(m):
    """r with r^2+r+1 = 0 mod m (m prime = 1 mod 3), r != 1."""
    if m == 1: return 0
    for r in range(2, m):
        if (r * r + r + 1) % m == 0: return r
    raise ValueError('no cube root of unity mod %d' % m)

def labels(gens, cyc, m, ts):
    """ts: list, one t per 3-cycle (in cyc order with len 3); fixed points get z=0."""
    r = root3(m); z = {}
    k = 0
    for c in cyc:
        if len(c) == 1:
            z[c[0]] = 0
        else:
            t = ts[k] % m; k += 1
            z[c[0]] = t; z[c[1]] = r * t % m; z[c[2]] = r * r * t % m
    return z

def lines(p, q, m, ts=None):
    gens = parse(p, q)
    perm, cyc = orbits(gens)
    n3 = sum(1 for c in cyc if len(c) == 3)
    if ts is None: ts = [1] * n3
    z = labels(gens, cyc, m, ts)
    out = []
    for i, (quat, mat) in enumerate(gens):
        a, b, c, d = mat
        out.append('%d %d %d %d %d' % (a, b, c, d, z[i]))
    return out, cyc

if __name__ == '__main__':
    p, q, m = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    ts = [int(x) for x in sys.argv[4:]] or None
    L, cyc = lines(p, q, m, ts)
    print('\n'.join(L))
