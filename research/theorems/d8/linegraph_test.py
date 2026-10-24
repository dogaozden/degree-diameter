"""Test the line-digraph idea: X = Z_5 polygon cover of H(q) (random matchings, degree q+3, diameter 7).
G = an Eulerian orientation of X (q+3 even, i.e. q odd).  U(L(G)): vertices = arcs u->w, a ~ b iff head(a) = tail(b).
It is bipartite (colour an arc by its tail) and (q+3)-regular with |E(X)| vertices.  We compute its diameter
(liftdiam with the trivial group).  Also V(X) u A(G) variants are printed for comparison of orders."""
import random, subprocess, sys
import gh
SCR = '/tmp/claude-0/-home-user-degree-diameter/0ad899b8-ae47-58b5-b704-0795802a53c1/scratchpad'
q = int(sys.argv[1]); seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
H = gh.load(q); N = H.N; I = 2 * N
rng = random.Random(seed)
# polygon cover X: vertices (v, i), i in Z_5
def vid(v, i): return v * 5 + (i % 5)
adj = [[] for _ in range(I * 5)]
for (p, L) in gh.flags(H):
    for i in range(5):
        adj[vid(p, i)].append(vid(L, i)); adj[vid(L, i)].append(vid(p, i))
for t in (1, 2):
    perm = list(range(N)); rng.shuffle(perm)
    for p in range(N):
        for i in range(5):
            a, b = vid(p, i), vid(N + perm[p], i + t)
            adj[a].append(b); adj[b].append(a)
V = I * 5
deg = set(len(x) for x in adj); assert deg == {q + 3}, deg
# Eulerian orientation via Hierholzer on each component (iterative)
used = {}
eid = {}
edges = []
for u in range(V):
    for w in adj[u]:
        if u < w:
            eid[(u, w)] = len(edges); edges.append((u, w))
# multigraph safety: polygon cover with random matchings may create parallel edges; skip check
ptr = [0] * V
nbr_e = [[] for _ in range(V)]
for k, (u, w) in enumerate(edges):
    nbr_e[u].append((w, k)); nbr_e[w].append((u, k))
usedE = [False] * len(edges)
arcs = []
for s in range(V):
    if ptr[s] >= len(nbr_e[s]):
        continue
    stack = [s]; path = []
    while stack:
        v = stack[-1]
        while ptr[v] < len(nbr_e[v]) and usedE[nbr_e[v][ptr[v]][1]]:
            ptr[v] += 1
        if ptr[v] == len(nbr_e[v]):
            path.append(stack.pop())
        else:
            w, k = nbr_e[v][ptr[v]]; usedE[k] = True; stack.append(w)
    path.reverse()
    for a, b in zip(path, path[1:]):
        arcs.append((a, b))
assert len(arcs) == len(edges)
outd = [0] * V
for a, b in arcs: outd[a] += 1
assert set(outd) == {(q + 3) // 2}, set(outd)
# line digraph underlying graph
by_tail = [[] for _ in range(V)]
for k, (a, b) in enumerate(arcs): by_tail[a].append(k)
E2 = []
for k, (a, b) in enumerate(arcs):
    for k2 in by_tail[b]:
        E2.append((k, k2))
path = f'{SCR}/ulg_q{q}_s{seed}.txt'
with open(path, 'w') as fh:
    fh.write(f'{len(arcs)} 1 1 {len(E2)}\n')
    for k, k2 in E2: fh.write(f'{k} {k2} 0 0\n')
print(f'q={q}: X has {V} vertices, degree {q+3}; arcs {len(arcs)} = |E(X)|; |V|+|E| = {V + len(arcs)} '
      f'(DGQ formula {5 * ((q + 5) // 2) * I})')
for D in (8, 9, 10):
    out = subprocess.run(['./liftdiam', path, str(D), '4'], capture_output=True, text=True).stdout.strip().split('\n')
    print('  U(L(G)):', out[0][:60], '|', out[1])
