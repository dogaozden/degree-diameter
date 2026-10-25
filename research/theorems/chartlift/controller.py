"""Controllers: k-regular bipartite graphs with a proper k-edge-colouring.
read_graph: record JSON ({'output': [n, edges]} or [n, edges]) or an edge list "n\\nu v\\n...".
bipartition + proper edge colouring by peeling perfect matchings (Hopcroft-Karp-free augmenting paths; fine at
these sizes; a k-regular bipartite multigraph always has a perfect matching, so the peeling never fails)."""
import json, random, sys
from collections import deque

def read_graph(path):
    txt = open(path).read()
    if txt.lstrip().startswith('{') or txt.lstrip().startswith('['):
        d = json.loads(txt)
        if isinstance(d, dict): d = d['output']
        if isinstance(d, str): d = json.loads(d)
        return d[0], [tuple(e) for e in d[1]]
    lines = [l for l in txt.split('\n') if l.strip() and not l.startswith('#')]
    n = int(lines[0].split()[0]); E = [tuple(map(int, l.split()[:2])) for l in lines[1:]]
    return n, E

def bipartition(n, E):
    adj = [[] for _ in range(n)]
    for u, v in E: adj[u].append(v); adj[v].append(u)
    side = [-1] * n
    for s in range(n):
        if side[s] >= 0: continue
        side[s] = 0; dq = deque([s])
        while dq:
            x = dq.popleft()
            for y in adj[x]:
                if side[y] < 0: side[y] = 1 - side[x]; dq.append(y)
                elif side[y] == side[x]: raise ValueError('not bipartite')
    return side

def proper_colouring(n, E, k, seed=0):
    """returns (Aside list, Bside list, coloured edges [(a_index, b_index, colour)]) with a proper k-edge-colouring"""
    side = bipartition(n, E)
    As = [v for v in range(n) if side[v] == 0]; Bs = [v for v in range(n) if side[v] == 1]
    ia = {v: i for i, v in enumerate(As)}; ib = {v: i for i, v in enumerate(Bs)}
    edges = [(ia[u], ib[v]) if side[u] == 0 else (ia[v], ib[u]) for u, v in E]
    deg = [0] * n
    for u, v in E: deg[u] += 1; deg[v] += 1
    assert min(deg) == max(deg) == k, 'controller must be k-regular'
    rng = random.Random(seed); m = len(As)
    remaining = list(range(len(edges))); col = [None] * len(edges)
    for c in range(k):
        inc = [[] for _ in range(m)]
        for e in remaining: inc[edges[e][0]].append(e)
        for l in inc: rng.shuffle(l)
        matchB = [-1] * m
        def aug(a, seen):
            for e in inc[a]:
                b = edges[e][1]
                if b in seen: continue
                seen.add(b)
                if matchB[b] < 0 or aug(edges[matchB[b]][0], seen):
                    matchB[b] = e; return True
            return False
        sys.setrecursionlimit(10000)
        order = list(range(m)); rng.shuffle(order)
        for a in order:
            assert aug(a, set()), 'no perfect matching'
        for b in range(m): col[matchB[b]] = c
        remaining = [e for e in remaining if col[e] is None]
    return As, Bs, [(a, b, col[i]) for i, (a, b) in enumerate(edges)]
