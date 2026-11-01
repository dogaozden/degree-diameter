#!/usr/bin/env python3
"""Build a (17,5) graph: the (16,5) route-chart graph G on 33,792 vertices plus "hubs" (job beyond-small, 2026-11-01).

G is built by research/theorems/graphs/build_d16D5_n33792.py (self-contained; K3,3 with a doubled perfect matching
lifted by Z22, fibre F4^4). A hub is a new vertex joined to a set N of old vertices of one side (|N| <= 17); every old
vertex lies in at most one N, so all degrees stay <= 17. Hub files: one hub per line, the global ids of N.
Orbit files (option --orbits): one base set N per line; the 22 hubs N+t are obtained by the automorphism
g -> g+t of G's controller coordinate (vertex ((a_i,g),x) -> ((a_i,g+t),x)).

Proposition (checked here before writing, and implied by diameter 5 of the result):
  if G is bipartite with diameter 5 and every hub on side S satisfies
    (1) every S-vertex is within distance 3 of N (cover), and
    (2) any two hubs on side S have x in N(h), x' in N(h') with d_G(x, x') <= 2,
  then G + hubs has diameter <= 5. (Old pairs keep their distance; a hub reaches S within 4 by (1) and the other side
  within 5 because same-side distances in G are <= 4; same-side hubs are within 4 by (2); a hub on side A reaches
  every A-vertex within 4, hence every hub on side B, which has an A-neighbour, within 5.)
usage: python3 build_d17D5_hubs.py OUT.edges [--orbits] HUBFILE [HUBFILE ...]   (--orbits applies to the files after it)
"""
import sys, os, importlib.util
H = 16896

def load_G():
    here = os.path.dirname(os.path.abspath(__file__))
    p = os.path.join(here, '..', '..', '..', 'theorems', 'graphs', 'build_d16D5_n33792.py')
    spec = importlib.util.spec_from_file_location('g16', p); m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
    return m.build()

def sh(w, t):
    off = 0 if w < H else H
    blk, y = divmod(w - off, 256); j, h = divmod(blk, 22)
    return off + (j * 22 + (h + t) % 22) * 256 + y

def main():
    out = sys.argv[1]; hubs = []; orb = False
    for a in sys.argv[2:]:
        if a == '--orbits': orb = True; continue
        for l in open(a):
            N = [int(x) for x in l.split()]
            if not N: continue
            if orb: hubs += [[sh(w, t) for w in N] for t in range(22)]
            else: hubs.append(N)
    n0, E = load_G()
    adj = [[] for _ in range(n0)]
    for u, v in E: adj[u].append(v); adj[v].append(u)
    used = set()
    for N in hubs:
        assert len(N) <= 17 and len(set(N)) == len(N)
        assert all(x < H for x in N) or all(x >= H for x in N), 'hub with neighbours on both sides'
        for x in N: assert x not in used, 'old vertex in two hubs'; used.add(x)
    # (1) cover: every vertex of the hub's side within distance 3 of N
    def ball(N, r):
        seen = set(N); fr = list(N)
        for _ in range(r):
            nx = []
            for x in fr:
                for y in adj[x]:
                    if y not in seen: seen.add(y); nx.append(y)
            fr = nx
        return seen
    bad1 = 0; R2 = []
    for N in hubs:
        S0 = 0 if N[0] >= H else H            # side of the hub = side opposite to N
        b3 = ball(N, 3); cov = sum(1 for z in b3 if S0 <= z < S0 + H)
        if cov != H: bad1 += 1
        R2.append(ball(N, 2))
    # (2) pairwise: same-side hubs have neighbours at distance <= 2
    bad2 = 0
    for i in range(len(hubs)):
        for j in range(i + 1, len(hubs)):
            if (hubs[i][0] >= H) != (hubs[j][0] >= H): continue
            if not any(x in R2[i] for x in hubs[j]): bad2 += 1
    print(f'hubs {len(hubs)}: cover failures {bad1}, incompatible same-side pairs {bad2}')
    with open(out, 'w') as f:
        f.write(f'{n0 + len(hubs)}\n'); f.writelines(f'{u} {v}\n' for u, v in E)
        for k, N in enumerate(hubs): f.writelines(f'{n0 + k} {x}\n' for x in N)
    print('vertices', n0 + len(hubs), 'edges', len(E) + sum(len(N) for N in hubs))

if __name__ == '__main__':
    main()
