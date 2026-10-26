# Gadget builder: +2 vertices on the cubic bipartite seed; cost = ordered pairs at distance > 7.
import sys, random, itertools, collections

def load(path):
    L = open(path).read().split()
    n = int(L[0]); E = [(int(L[1+2*i]), int(L[2+2*i])) for i in range((len(L)-1)//2)]
    return n, E

def colour(n, E):
    adj = collections.defaultdict(list)
    for a, b in E: adj[a].append(b); adj[b].append(a)
    col = {0: 0}; q = [0]
    for x in q:
        for y in adj[x]:
            if y not in col: col[y] = 1 - col[x]; q.append(y)
    return col

def relabel(n, E):
    """return (n, edges as (white, black)) with white = 0..n/2-1 and black = n/2..n-1"""
    col = colour(n, E); m = n // 2
    w = [v for v in range(n) if col[v] == 0]; b = [v for v in range(n) if col[v] == 1]
    assert len(w) == m and len(b) == m
    mp = {v: i for i, v in enumerate(w)}; mp.update({v: m + i for i, v in enumerate(b)})
    return n, [tuple(sorted((mp[a], mp[c]))) for a, c in ((x, y) if col[x] == 0 else (y, x) for x, y in E)]

def cost(n, E, D=7):
    nb = [[] for _ in range(n)]
    for a, b in E: nb[a].append(b); nb[b].append(a)
    cur = [1 << x for x in range(n)]
    for _ in range(D):
        cur = [cur[x] | cur[nb[x][0]] | cur[nb[x][1]] | (cur[nb[x][2]] if len(nb[x]) > 2 else 0) for x in range(n)]
    full = (1 << n) - 1
    return sum(n - bin(c).count('1') for c in cur)

def gadget(n, E, a1, b1, a2, b2):
    """E is list of (white, black). Delete a1b1, a2b2; add x (white n) y (black n+1)."""
    S = set(E)
    assert (a1, b1) in S and (a2, b2) in S and len({a1, a2, b1, b2}) == 4
    assert (a1, b2) not in S and (a2, b1) not in S
    x, y = n, n + 1
    E2 = [e for e in E if e not in ((a1, b1), (a2, b2))]
    E2 += [(x, y), (x, b1), (x, b2), (a1, y), (a2, y)]
    return n + 2, [tuple(sorted(e)) for e in E2]

def write(path, n, E):
    with open(path, 'w') as f:
        f.write(f"{n}\n")
        for a, b in E: f.write(f"{a} {b}\n")

def dist_between(n, E, e1, e2):
    nb = [[] for _ in range(n)]
    for a, b in E: nb[a].append(b); nb[b].append(a)
    src = set(e1); d = {v: 0 for v in src}; q = list(src)
    for x in q:
        for y in nb[x]:
            if y not in d: d[y] = d[x] + 1; q.append(y)
    return min(d[v] for v in e2)

if __name__ == '__main__':
    n0, E0 = load('/home/user/degree-diameter/research/d3D7/seeds/conder168.edges')
    n0, E0 = relabel(n0, E0)
    print('seed cost', cost(n0, E0), 'n', n0)
