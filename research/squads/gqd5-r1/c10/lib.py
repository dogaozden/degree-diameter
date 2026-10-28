import sys, os, subprocess, random, itertools
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
HUB4 = os.path.join(HERE, 'hub4')

def write_graph(path, n, edges):
    with open(path, 'w') as f:
        f.write(f"{n} {len(edges)}\n")
        f.write("".join(f"{u} {v}\n" for u, v in edges))

def check(n, edges, tag=None):
    """Runs the C same-colour checker. Returns dict."""
    p = os.path.join(HERE, f"tmp_{os.getpid()}.txt") if tag is None else os.path.join(HERE, tag)
    write_graph(p, n, edges)
    out = subprocess.run([HUB4, p], capture_output=True, text=True).stdout.strip()
    if tag is None:
        os.remove(p)
    d = dict(kv.split('=') for kv in out.split()[1:])
    return {k: (int(v) if v.lstrip('-').isdigit() else v) for k, v in d.items()}

def gq_incidence(G):
    """Vertices: points 0..np-1, lines np..np+nl-1. Returns n, edges, nP, nL."""
    edges = []
    for l, pts in enumerate(G.lines):
        for p in pts:
            edges.append((p, G.np + l))
    return G.np + G.nl, edges

def level_graph(G, r, rng):
    """2r+1 copies of the incidence graph of GQ G, all levels type H (A = points), cyclic matchings
    from A-elements of level j to B-elements of level j+k (k=1..r) by random bijections."""
    L = 2 * r + 1
    N = G.np  # = G.nl for order (s,s)
    per = 2 * N
    edges = []
    for j in range(L):
        b = j * per
        for p, ls in enumerate(G.plines):
            for l in ls:
                edges.append((b + p, b + N + l))
    for j in range(L):
        for k in range(1, r + 1):
            perm = list(range(N)); rng.shuffle(perm)
            b2 = ((j + k) % L) * per
            for p in range(N):
                edges.append((j * per + p, b2 + N + perm[p]))
    return L * per, edges, L * N, L * N

def pg2_incidence(p, pendants=False):
    """PG(2,p) for prime p. Points 0..N-1, lines N..2N-1. Optional pendant at each point (node 2N+x, line-colour)
    and at each line (node 3N+L, point-colour)."""
    pts = []
    for a in range(p):
        for b in range(p):
            pts.append((1, a, b))
    for b in range(p):
        pts.append((0, 1, b))
    pts.append((0, 0, 1))
    N = len(pts)
    edges = []
    for i, x in enumerate(pts):
        for j, y in enumerate(pts):
            if (sum(u * v for u, v in zip(x, y)) % p) == 0:
                edges.append((i, N + j))
    n = 2 * N
    if pendants:
        for x in range(N):
            edges.append((x, 2 * N + x))
        for l in range(N):
            edges.append((N + l, 3 * N + l))
        n = 4 * N
    return n, edges, N, N

def random_regular_bip(K, d, rng, tries=300):
    """Union of d random perfect matchings between K A-vertices and K B-vertices, simple (each
    matching avoids earlier edges). Returns edges or None."""
    used = np.zeros((K, K), dtype=bool)
    edges = []
    for _ in range(d):
        ok = False
        for _t in range(tries):
            perm = np.array(rng.sample(range(K), K))
            if not used[np.arange(K), perm].any():
                ok = True; break
        if not ok:
            return None
        used[np.arange(K), perm] = True
        edges += [(a, K + int(perm[a])) for a in range(K)]
    return edges

def random_maximal_bip(KA, KB, d, rng):
    """Greedy maximal bipartite subgraph with max degree <= d on both sides (random order)."""
    pairs = [(a, b) for a in range(KA) for b in range(KB)]
    rng.shuffle(pairs)
    dA = [0] * KA; dB = [0] * KB; edges = []
    for a, b in pairs:
        if dA[a] < d and dB[b] < d:
            dA[a] += 1; dB[b] += 1; edges.append((a, KA + b))
    return edges

def hub_edges_to_graph(KA, KB, edges):
    """Vertices: A = 0..KA-1, B = KA..KA+KB-1 (edges given as (a, KA+b)). Returns n, edges."""
    return KA + KB, edges
