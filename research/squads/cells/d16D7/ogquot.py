#!/usr/bin/env python3
"""ogquot.py: quotient of an orbit graph by extra collineations that normalise G = <g>.
usage: ogquot.py GRAPH GPERM.bin OUT_QUOT OUT_MAP PERM1.bin [PERM2.bin ...]
  GRAPH: og_pts.txt / og_lines.txt ("M E", then "idx rep deg nbrs...", rep = smallest element of the g-orbit);
  GPERM.bin: int32 permutation of the elements (g); PERMi.bin: other collineations (int32 element permutations) that map
  g-orbits to g-orbits (h = data/g13o183_*.bin, F = data/F13_*.bin). Each induces a permutation of the orbit-graph
  vertices; the group they generate is applied, and its orbits that contain no edge become quotient vertices.
  OUT_QUOT: "n" then per quotient vertex "w deg nbr1 ... nbr_deg" (w = number of orbit-graph vertices in it);
  OUT_MAP: per quotient vertex one line with its orbit-graph vertex indices. A quotient independent set expands to an
  orbit-graph independent set of total weight (expand with ogquot_expand.py)."""
import sys
import numpy as np


def main():
    g, gperm, outq, outm = sys.argv[1:5]
    perms = sys.argv[5:]
    with open(g) as f:
        M, E = map(int, f.readline().split())
        rep = np.zeros(M, dtype=np.int64)
        nb = [None] * M
        for line in f:
            a = list(map(int, line.split()))
            rep[a[0]] = a[1]
            nb[a[0]] = a[3:3 + a[2]]
    P = np.fromfile(gperm, dtype=np.int32).astype(np.int64)
    N = len(P)
    # g-orbit minimum of every element
    mn = np.arange(N)
    cur = np.arange(N)
    for _ in range(200):
        cur = P[cur]
        mn = np.minimum(mn, cur)
        if np.array_equal(cur, np.arange(N)):
            break
    vid = -np.ones(N, dtype=np.int64)       # element (orbit minimum) -> orbit-graph vertex
    vid[rep] = np.arange(M)
    gens = []
    for pf in perms:
        Q = np.fromfile(pf, dtype=np.int32).astype(np.int64)
        img = vid[mn[Q[rep]]]
        if np.any(img < 0):
            print('warning: %s maps %d good orbits outside the graph; ignored' % (pf, int((img < 0).sum())))
            continue
        assert len(np.unique(img)) == M, 'not a permutation of the orbit-graph vertices'
        # check it is an automorphism of the orbit graph
        S = [set(x) for x in nb]
        bad = sum(1 for v in range(M) for u in nb[v] if img[u] not in S[img[v]])
        assert bad == 0, 'not an automorphism (%d bad edges)' % bad
        gens.append(img)
    # orbits of the generated group (union-find over generators)
    par = np.arange(M)
    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for img in gens:
        for v in range(M):
            a, b = find(v), find(int(img[v]))
            if a != b:
                par[a] = b
    roots = np.array([find(v) for v in range(M)])
    groups = {}
    for v in range(M):
        groups.setdefault(int(roots[v]), []).append(v)
    qv = []
    for r, mem in groups.items():
        ms = set(mem)
        if any(u in ms for v in mem for u in nb[v]):
            continue
        qv.append(sorted(mem))
    qid = -np.ones(M, dtype=np.int64)
    for i, mem in enumerate(qv):
        qid[mem] = i
    sizes = {}
    for mem in qv:
        sizes[len(mem)] = sizes.get(len(mem), 0) + 1
    with open(outq, 'w') as f, open(outm, 'w') as fm:
        f.write('%d\n' % len(qv))
        for i, mem in enumerate(qv):
            ns = sorted(set(int(qid[u]) for v in mem for u in nb[v] if qid[u] >= 0) - {i})
            f.write('%d %d %s\n' % (len(mem), len(ns), ' '.join(map(str, ns))))
            fm.write(' '.join(map(str, mem)) + '\n')
    print('group orbits: %d (dropped %d with an internal edge); quotient vertices %d, sizes %s' % (len(groups), len(groups) - len(qv), len(qv), sizes))


if __name__ == '__main__':
    main()
