#!/usr/bin/env python3
"""Rebuild Conder's (3,7) graph (168 vertices) as the lift in research/lifts/sols/rebuild_d3D7_n168_b2_3_0_meta732xcyc2.txt
(branch claude/voltage-lifts-search-6lfotq) and count, for every same-side pair, nonbacktracking walks of length 2,4,6.
Question: can it be a route-chart controller over F_4^6 (Delta = 12, D = 7, 2*84*4096 = 688,128 vertices)?"""
import itertools, collections, sys
# group (Z7 x| Z3) x Z2, elements (a, j, c)
def mul(x, y, conv):
    a, j, c = x; b, l, d = y
    if conv == 0:
        return ((a + pow(2, j, 7) * b) % 7, (j + l) % 3, (c + d) % 2)
    else:
        return ((pow(2, l, 7) * a + b) % 7, (j + l) % 3, (c + d) % 2)
G = [(a, j, c) for a in range(7) for j in range(3) for c in range(2)]
base_edges = [(0, 2, (0, 0, 0)), (0, 2, (4, 1, 1)), (0, 3, (0, 0, 0)), (1, 2, (0, 0, 0)), (1, 3, (2, 2, 0)), (1, 3, (2, 0, 1))]
def build(conv, side):
    idx = {}
    for u in range(4):
        for g in G:
            idx[(u, g)] = len(idx)
    adj = [[] for _ in idx]
    for (u, v, g) in base_edges:
        for h in G:
            x, y = idx[(u, h)], idx[(v, mul(h, g, conv) if side == 0 else mul(g, h, conv))]
            adj[x].append(y); adj[y].append(x)
    return adj
def bfs(adj, s):
    d = [-1] * len(adj); d[s] = 0; q = [s]
    for x in q:
        for y in adj[x]:
            if d[y] < 0:
                d[y] = d[x] + 1; q.append(y)
    return d
for conv in (0, 1):
    for side in (0, 1):
        adj = build(conv, side)
        n = len(adj)
        diam = max(max(bfs(adj, s)) for s in range(n))
        print('conv', conv, 'side', side, 'n', n, 'diameter', diam, 'deg', set(len(a) for a in adj))
        if diam != 7:
            continue
        # girth
        girth = 99
        for s in range(n):
            d = [-1]*n; par = [-1]*n; d[s] = 0; q = [s]
            for x in q:
                for y in adj[x]:
                    if d[y] < 0:
                        d[y] = d[x]+1; par[y] = x; q.append(y)
                    elif par[x] != y:
                        girth = min(girth, d[x]+d[y]+1)
        print('  girth', girth)
        # nonbacktracking walk counts from each vertex to each same-side vertex, lengths 2,4,6
        stats = collections.Counter()
        nb6_by_dist = collections.defaultdict(list)
        for s in range(n):
            d = bfs(adj, s)
            # NB walks: state (prev, cur)
            cnt = {(-1, s): 1}
            per_len = {}
            for L in range(1, 7):
                nc = collections.Counter()
                for (p, c), m in cnt.items():
                    for y in adj[c]:
                        if y != p:
                            nc[(c, y)] += m
                cnt = nc
                if L % 2 == 0:
                    end = collections.Counter()
                    for (p, c), m in cnt.items():
                        end[c] += m
                    per_len[L] = end
            for t in range(n):
                if d[t] % 2 == 1:
                    continue
                nb6_by_dist[d[t]].append(per_len[6].get(t, 0))
        for dist in sorted(nb6_by_dist):
            arr = nb6_by_dist[dist]
            print(f'  same-side pairs at distance {dist}: {len(arr)//n} per vertex; NB 6-walks min {min(arr)} mean {sum(arr)/len(arr):.2f} '
                  f'zero-count {sum(1 for a in arr if a==0)}')
        sys.exit(0)
