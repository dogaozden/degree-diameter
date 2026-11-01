"""Small graph utilities for deep-37 (edge-list format: first token n, then pairs)."""
import subprocess, collections, itertools
def load(fn):
    t = open(fn).read().split()
    n = int(t[0]); E = [(int(t[i]), int(t[i+1])) for i in range(1, len(t), 2)]
    adj = [[] for _ in range(n)]
    for a, b in E: adj[a].append(b); adj[b].append(a)
    return n, E, adj
def save(fn, n, E):
    with open(fn, 'w') as f:
        f.write(f"{n}\n"); [f.write(f"{a} {b}\n") for a, b in sorted(tuple(sorted(e)) for e in E)]
def bfs(adj, s, cap=99):
    d = {s: 0}; q = [s]
    for u in q:
        if d[u] >= cap: continue
        for w in adj[u]:
            if w not in d: d[w] = d[u] + 1; q.append(w)
    return d
def dist_matrix(adj):
    n = len(adj); D = [[99]*n for _ in range(n)]
    for s in range(n):
        for v, x in bfs(adj, s).items(): D[s][v] = x
    return D
def sides(adj):
    n = len(adj); c = [-1]*n; c[0] = 0; q = [0]
    for u in q:
        for w in adj[u]:
            if c[w] < 0: c[w] = 1 - c[u]; q.append(w)
    return c
def aut_gens(adj, partition=None):
    """automorphism generators via dreadnaut; returns list of permutations (lists)"""
    n = len(adj)
    s = f"n={n} g\n" + ";\n".join(" ".join(map(str, sorted(adj[v]))) for v in range(n)) + ".\n"
    if partition: s += "f=[" + "|".join(",".join(map(str, c)) for c in partition) + "]\n"
    s += "-m x\n"   # quiet, run
    out = subprocess.run(["dreadnaut"], input=s, capture_output=True, text=True).stdout
    gens = []
    for ln in out.splitlines():
        if ln.startswith("("): gens.append(ln)
        elif ln.startswith(" ") and gens and "orbit" not in ln and "cpu" not in ln: gens[-1] += " " + ln
    perms = []
    for gtxt in gens:
        p = list(range(n))
        for cyc in gtxt.replace("\n", " ").split(")"):
            cyc = cyc.replace("(", " ").split()
            if not cyc: continue
            c = list(map(int, cyc))
            for i in range(len(c)): p[c[i]] = c[(i+1) % len(c)]
        perms.append(p)
    import re
    m = re.search(r"grpsize=([0-9.e+]+)", out)
    return perms, (m.group(1) if m else None), out
def group_closure(perms, n, limit=200000):
    idp = tuple(range(n)); G = {idp}; frontier = [idp]
    gens = [tuple(p) for p in perms]
    while frontier:
        nf = []
        for g in frontier:
            for h in gens:
                k = tuple(h[g[i]] for i in range(n))
                if k not in G: G.add(k); nf.append(k)
        frontier = nf
        if len(G) > limit: raise RuntimeError("group too big")
    return list(G)
def orbits_of(perms, n):
    par = list(range(n))
    def f(x):
        while par[x] != x: par[x] = par[par[x]]; x = par[x]
        return x
    for p in perms:
        for i in range(n): a, b = f(i), f(p[i]); par[a] = b
    O = collections.defaultdict(list)
    for i in range(n): O[f(i)].append(i)
    return sorted(O.values(), key=lambda o: (len(o), o))
