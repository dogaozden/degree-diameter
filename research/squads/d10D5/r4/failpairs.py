#!/usr/bin/env python3
"""failpairs.py X.edges [N]: list lift-vertex pairs at distance > 5 (sources (x,0) only; vertex (x,h) = 6x+h, x < 2N lift)"""
import sys, collections
import numpy as np
fn = sys.argv[1]; N = int(sys.argv[2]) if len(sys.argv) > 2 else 400
ls = open(fn).read().split(); n = int(ls[0]); E = np.array(ls[1:], dtype=np.int64).reshape(-1, 2)
adj = [[] for _ in range(n)]
for a, b in E: adj[a].append(b); adj[b].append(a)
lift = 2 * N * 6; out = collections.Counter()
for s in list(range(0, lift, 6)) + list(range(lift, n)):
    d = np.full(n, -1); d[s] = 0; fr = [s]
    for k in range(5):
        nx = []
        for x in fr:
            for y in adj[x]:
                if d[y] < 0: d[y] = k + 1; nx.append(y)
        fr = nx
    for t in np.nonzero(d < 0)[0]:
        def name(v): return ('hub%d' % (v - lift)) if v >= lift else (('P%d' % (v // 6)) if v // 6 < N else ('L%d' % (v // 6 - N))) + '.%d' % (v % 6)
        print(name(s), name(int(t)))
