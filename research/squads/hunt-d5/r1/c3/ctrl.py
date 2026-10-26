"""Shared helpers for card c3: cubic bipartite graphs on 2m vertices.
Side A = 0..m-1, side B = m..2m-1. Adjacency as int bitmasks."""
import random

def popc(x):
    return bin(x).count('1')

def bits(x):
    out = []
    while x:
        lb = x & -x
        out.append(lb.bit_length() - 1)
        x ^= lb
    return out

def ball2(adj):
    n = len(adj)
    b2 = [0] * n
    for v in range(n):
        r = (1 << v) | adj[v]
        for u in bits(adj[v]):
            r |= adj[u]
        b2[v] = r
    return b2

def cost(adj, m, wc=1):
    """Number of ordered same-side pairs at distance > 4, plus wc per vertex on no 4-cycle."""
    n = 2 * m
    b2 = ball2(adj)
    SA = (1 << m) - 1
    SB = SA << m
    c = 0
    for v in range(n):
        r = 0
        for u in bits(b2[v]):
            r |= b2[u]
        side = SA if v < m else SB
        c += popc(side & ~r)
    for v in range(n):
        nb = bits(adj[v])
        ok = False
        for i in range(len(nb)):
            for j in range(i + 1, len(nb)):
                if popc(adj[nb[i]] & adj[nb[j]]) >= 2:
                    ok = True
                    break
            if ok:
                break
        if not ok:
            c += wc
    return c

def c4_count(adj, v):
    """Number of 4-cycles through v: pairs of neighbours x,y of v with w != v common to both."""
    nb = bits(adj[v])
    tot = 0
    for i in range(len(nb)):
        for j in range(i + 1, len(nb)):
            tot += popc(adj[nb[i]] & adj[nb[j]]) - 1
    return tot

def from_edges(m, edges):
    adj = [0] * (2 * m)
    for a, b in edges:
        adj[a] |= 1 << (m + b)
        adj[m + b] |= 1 << a
    return adj

def to_edges(m, adj):
    return [(a, b - m) for a in range(m) for b in bits(adj[a])]

def haar_adj(m, table_N, table, S):
    """Haar graph H(G,S): A-vertex g ~ B-vertex s*g, table[x*N+y] = x*y (identity 0), N = m."""
    adj = [0] * (2 * m)
    for g in range(m):
        for s in S:
            b = table[s * m + g]
            adj[g] |= 1 << (m + b)
            adj[m + b] |= 1 << g
    return adj

def write_edges(path, m, adj):
    with open(path, 'w') as f:
        f.write(f"{2*m}\n")
        for a, b in to_edges(m, adj):
            f.write(f"{a} {m + b}\n")

def random_cubic_bip(m, rng):
    """Random simple cubic bipartite graph as union of 3 perfect matchings (retry on multi-edge)."""
    while True:
        adj = [0] * (2 * m)
        ok = True
        for _ in range(3):
            perm = list(range(m))
            rng.shuffle(perm)
            for a in range(m):
                b = perm[a]
                if (adj[a] >> (m + b)) & 1:
                    ok = False
                    break
                adj[a] |= 1 << (m + b)
                adj[m + b] |= 1 << a
            if not ok:
                break
        if ok:
            return adj

def switch_move(adj, m, rng):
    """Random edge switch a1b1,a2b2 -> a1b2,a2b1 keeping simple cubic bipartite. Returns new adj or None."""
    a1 = rng.randrange(m)
    nb1 = bits(adj[a1])
    b1 = rng.choice(nb1) - m
    a2 = rng.randrange(m)
    if a2 == a1:
        return None
    nb2 = bits(adj[a2])
    b2 = rng.choice(nb2) - m
    if b1 == b2:
        return None
    if (adj[a1] >> (m + b2)) & 1 or (adj[a2] >> (m + b1)) & 1:
        return None
    new = adj[:]
    new[a1] ^= (1 << (m + b1)) | (1 << (m + b2))
    new[a2] ^= (1 << (m + b2)) | (1 << (m + b1))
    new[m + b1] ^= (1 << a1) | (1 << a2)
    new[m + b2] ^= (1 << a1) | (1 << a2)
    return new
