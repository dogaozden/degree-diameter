"""Clique of PG(2,s_k) cores joined pairwise by cross edges (explicit up to a deterministic search).

Core k: PG(2,s_k) incidence; A-vertices = points, B-vertices = lines.
Every core k chooses, for every other core j, a centre c(k,j) (a point of core k) and a line l(k,j) (a line of core k).
  Pen(k,j) = lines of core k through c(k,j)     (s_k+1 lines, B-side)
  Pts(k,j) = points of core k on l(k,j)        (s_k+1 points, A-side)
For each unordered pair {i,j}:
  E_B(i,j): join Pen(i,j) (lines of i) to Pts(j,i) (points of j); e = max(s_i+1, s_j+1) edges, edge t joins
            Pen[t % a] and Pts[t % b].
  E_A(i,j): join Pts(i,j) (points of i) to Pen(j,i) (lines of j); same rule.
Every vertex gets at most delta-(s+1) cross edges (so max degree <= delta).
Correctness of hub property (proof in construction.md): same-core pairs are at distance <= 2; for points p in i, p' in j,
the pencil Pen(i,j) covers all points of core i, so p - line - point(of j) - line - p' has length 4; the same for lines
(Pts(i,j) meets every line of core i).
"""
import random
from hubgen import pg2, Graph

def geometry(sizes):
    geo = []
    for s in sizes:
        N, lp = pg2(s)
        pl = [[] for _ in range(N)]
        for l, plist in enumerate(lp):
            for p in plist:
                pl[p].append(l)
        geo.append(dict(s=s, N=N, lp=lp, pl=pl, cap=None))
    return geo

def cross_edges(geo, cen, lin):
    """Return list of (side_i, idx_i, side_j, idx_j, i, j) with side 'P' (point) or 'L' (line)."""
    m = len(geo)
    out = []
    for i in range(m):
        for j in range(i + 1, m):
            # E_B(i,j): lines of i through cen[i,j]  with points of j on lin[j,i]
            pen = geo[i]['pl'][cen[(i, j)]]
            pts = geo[j]['lp'][lin[(j, i)]]
            a, b = len(pen), len(pts); e = max(a, b)
            for t in range(e):
                out.append(('L', i, pen[t % a], 'P', j, pts[t % b]))
            # E_A(i,j): points of i on lin[i,j] with lines of j through cen[j,i]
            pts = geo[i]['lp'][lin[(i, j)]]
            pen = geo[j]['pl'][cen[(j, i)]]
            a, b = len(pts), len(pen); e = max(a, b)
            for t in range(e):
                out.append(('P', i, pts[t % a], 'L', j, pen[t % b]))
    return out

def loads(geo, edges):
    m = len(geo)
    useP = [[0] * g['N'] for g in geo]
    useL = [[0] * g['N'] for g in geo]
    for (s1, c1, v1, s2, c2, v2) in edges:
        for side, c, v in ((s1, c1, v1), (s2, c2, v2)):
            (useP if side == 'P' else useL)[c][v] += 1
    return useP, useL

def find_choices(sizes, delta, seed=0, iters=200000):
    rnd = random.Random(seed)
    geo = geometry(sizes)
    m = len(sizes)
    for g in geo: g['cap'] = delta - g['s'] - 1
    if any(g['cap'] < 0 for g in geo):
        return None
    cen, lin = {}, {}
    for i in range(m):
        for j in range(m):
            if i != j:
                cen[(i, j)] = rnd.randrange(geo[i]['N'])
                lin[(i, j)] = rnd.randrange(geo[i]['N'])
    def over(cen, lin):
        useP, useL = loads(geo, cross_edges(geo, cen, lin))
        return sum(max(0, useP[c][v] - geo[c]['cap']) + max(0, useL[c][v] - geo[c]['cap'])
                   for c in range(m) for v in range(geo[c]['N'])), useP, useL
    cur, _, _ = over(cen, lin)
    keys = list(cen.keys())
    it = 0
    while cur > 0 and it < iters:
        it += 1
        key = rnd.choice(keys)
        old_c, old_l = cen[key], lin[key]
        if rnd.random() < 0.5:
            cen[key] = rnd.randrange(geo[key[0]]['N'])
        else:
            lin[key] = rnd.randrange(geo[key[0]]['N'])
        new, _, _ = over(cen, lin)
        if new <= cur or rnd.random() < 0.01:
            cur = new
        else:
            cen[key], lin[key] = old_c, old_l
    if cur > 0:
        return None
    return geo, cen, lin

def build_graph(sizes, delta, seed=0):
    res = find_choices(sizes, delta, seed)
    if res is None:
        return None
    geo, cen, lin = res
    G = Graph()
    ids = []
    for g in geo:
        pts = [G.add(0) for _ in range(g['N'])]
        lns = [G.add(1) for _ in range(g['N'])]
        for l, plist in enumerate(g['lp']):
            for p in plist:
                G.edge(pts[p], lns[l])
        ids.append((pts, lns))
    for (s1, c1, v1, s2, c2, v2) in cross_edges(geo, cen, lin):
        u = ids[c1][0][v1] if s1 == 'P' else ids[c1][1][v1]
        w = ids[c2][0][v2] if s2 == 'P' else ids[c2][1][v2]
        G.edge(u, w)
    return G
