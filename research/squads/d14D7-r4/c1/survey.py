# c1 (r4): survey the 23 isometry permutations of E11 (perms_q11), their orders, commuting pairs and
# generated group sizes. Read-only use of research/cell147/data. Output: printed summary + groups.json.
import glob, os, math, json, sys
from collections import Counter
import numpy as np
D = '/home/user/degree-diameter/research/cell147/data/'
OUT = '/home/user/degree-diameter/research/squads/d14D7-r4/c1/'

def load(path):
    return np.loadtxt(path, dtype=np.int64)

def cycles(p):
    n = len(p); seen = np.zeros(n, bool); out = []; pl = p.tolist()
    for i in range(n):
        if seen[i]: continue
        c = []; j = i
        while not seen[j]:
            seen[j] = True; c.append(j); j = pl[j]
        out.append(c)
    return out

def order_and_profile(p):
    cyc = cycles(p); o = 1
    for c in cyc: o = o * len(c) // math.gcd(o, len(c))
    return o, tuple(sorted(Counter(len(c) for c in cyc).items()))

def compose(a, b):  # a o b : i -> a[b[i]]
    return a[b]

def group_closure(gens, n, limit=4000):
    idp = np.arange(n, dtype=np.int64)
    seen = {idp.tobytes(): idp}; frontier = [idp]
    while frontier:
        nf = []
        for x in frontier:
            for g in gens:
                y = g[x]
                k = y.tobytes()
                if k not in seen:
                    seen[k] = y; nf.append(y)
                    if len(seen) > limit: return None
        frontier = nf
    return list(seen.values())

def orbits_of_gens(gens, n):
    parent = list(range(n))
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]; x = parent[x]
        return x
    for g in gens:
        for i, j in enumerate(g.tolist()):
            a, b = find(i), find(j)
            if a != b: parent[a] = b
    roots = {}
    orb = [0] * n
    for i in range(n):
        r = find(i)
        if r not in roots: roots[r] = len(roots)
        orb[i] = roots[r]
    k = len(roots)
    members = [[] for _ in range(k)]
    for i in range(n): members[orb[i]].append(i)
    return members

if __name__ == '__main__':
    files = sorted(glob.glob(D + 'perms_q11/*.txt'))
    P = {}
    for f in files:
        P[os.path.basename(f)[:-4]] = load(f)
    n = len(next(iter(P.values())))
    names = list(P)
    info = {}
    for k in names:
        p = P[k]
        assert len(p) == n and np.array_equal(np.sort(p), np.arange(n)), k
        o, prof = order_and_profile(p)
        info[k] = (o, prof)
        print(f"{k:22s} order {o:3d} profile {prof}")
    comm = []
    for a in range(len(names)):
        for b in range(a + 1, len(names)):
            g, h = P[names[a]], P[names[b]]
            if np.array_equal(g[h], h[g]):
                comm.append((names[a], names[b]))
    print("commuting pairs:", len(comm))
    res = []
    for (x, y) in comm:
        A = group_closure([P[x], P[y]], n)
        gs = None if A is None else len(A)
        if A is None:
            print(x, y, "group > 4000"); continue
        mem = orbits_of_gens([P[x], P[y]], n)
        sz = Counter(len(m) for m in mem)
        print(f"{x:22s} {y:22s} |G|={gs:4d} orbits={len(mem):5d} sizes={dict(sorted(sz.items()))}")
        res.append({"x": x, "y": y, "order_G": gs, "norb": len(mem)})
    json.dump({"orders": {k: [v[0], list(map(list, v[1]))] for k, v in info.items()}, "commuting": comm, "pairs": res}, open(OUT + 'survey.json', 'w'), indent=1)
