"""Card d2 (States = out-arcs + 2): base graph W = V(I) x {0,1} u A(G) on 2912 vertices, degree 6, bipartite.
I = incidence graph of H(3) (728 vertices, 4-regular), G = Eulerian orientation of I (out- and in-degree 2).
Rule:
  arc k=(t->h)     ~ out-arcs of h (2), in-arcs of t (2), copies (h,0),(h,1)          -> degree 6
  copy (v,i)       ~ in-arcs of v (2), copies (x,i) for x a neighbour of v in I (4)    -> degree 6
Vertex ids: copy (v,i) -> 2v+i (0..1455); arc k -> 1456+k (1456..2911).
Usage: python3 build_d2.py OUT_BASE_FILE [seed] [mode]   (writes liftdiam format, Z_5 with random voltages)
"""
import sys, random
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d8')
import gh

def eulerian_orientation(H, seed=1):
    N = H.N
    edges = gh.flags(H)                       # (point, N+line)
    V = 2 * N
    rng = random.Random(seed)
    edges = edges[:]
    rng.shuffle(edges)
    nbr = [[] for _ in range(V)]
    for k, (u, w) in enumerate(edges):
        nbr[u].append((w, k)); nbr[w].append((u, k))
    for x in nbr: rng.shuffle(x)
    ptr = [0] * V; used = [False] * len(edges); arcs = []
    for s in range(V):
        if ptr[s] >= len(nbr[s]): continue
        stack = [s]; path = []
        while stack:
            v = stack[-1]
            while ptr[v] < len(nbr[v]) and used[nbr[v][ptr[v]][1]]: ptr[v] += 1
            if ptr[v] == len(nbr[v]): path.append(stack.pop())
            else:
                w, k = nbr[v][ptr[v]]; used[k] = True; stack.append(w)
        path.reverse()
        arcs += list(zip(path, path[1:]))
    assert len(arcs) == len(edges)
    return arcs, N

def build_base(seed=1):
    H = gh.load(3)
    arcs, N = eulerian_orientation(H, seed)
    nA = len(arcs)
    assert nA == len(gh.flags(H))
    NC = 2 * (2 * N)              # copies: 2 per vertex of I (2N vertices)
    NW = NC + nA
    out_at = [[] for _ in range(2 * N)]; in_at = [[] for _ in range(2 * N)]
    for k, (t, h) in enumerate(arcs):
        out_at[t].append(NC + k); in_at[h].append(NC + k)
    E = []  # (u, v, group-label-type) ; type: 'aa' arc-arc, 'ac' arc-copy, 'cc' copy-copy
    for k, (t, h) in enumerate(arcs):
        E.append((NC + k, 2 * h + 0, 'ac'))
        E.append((NC + k, 2 * h + 1, 'ac'))
    for hv in range(2 * N):
        for a in in_at[hv]:
            for b in out_at[hv]:
                E.append((a, b, 'aa'))
    nbrs = [[] for _ in range(2 * N)]
    for k, (u, w) in enumerate(gh.flags(H)):
        nbrs[u].append(w); nbrs[w].append(u)
    for v in range(2 * N):
        for x in nbrs[v]:
            if v < x:
                for i in (0, 1):
                    E.append((2 * v + i, 2 * x + i, 'cc'))
    return NW, E, arcs, H

def bfs_diam(NW, E):
    adj = [[] for _ in range(NW)]
    for u, v, _ in E:
        adj[u].append(v); adj[v].append(u)
    diam = 0; ecc_hist = {}
    for s in range(0, NW, 1):
        d = [-1] * NW; d[s] = 0; q = [s]
        for x in q:
            for y in adj[x]:
                if d[y] < 0: d[y] = d[x] + 1; q.append(y)
        m = max(d)
        diam = max(diam, m)
    return diam

def write_lift_file(path, NW, E, volts, M=5):
    with open(path, 'w') as fh:
        fh.write(f'{NW} {M} 1 {len(E)}\n')
        for (u, v, _), a in zip(E, volts):
            fh.write(f'{u} {v} {a} 0\n')

if __name__ == '__main__':
    out = sys.argv[1]
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    NW, E, arcs, H = build_base(seed)
    deg = [0] * NW
    for u, v, _ in E: deg[u] += 1; deg[v] += 1
    print('NW', NW, 'edges', len(E), 'deg range', min(deg), max(deg))
    rng = random.Random(seed)
    volts = [rng.randrange(5) for _ in E]
    write_lift_file(out, NW, E, volts)
    print('base diameter', bfs_diam(NW, E))
