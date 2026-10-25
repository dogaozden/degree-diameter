"""Candidate with exactly the DGQ vertex count for odd q:
per Z_5-level: the arcs of an Eulerian orientation G of the H(q) incidence graph I ((q+1)P arcs) and two copies
x^1, x^2 of every element x (4P), i.e. (q+5)P vertices; arc u->w adjacent to its successors (w->*) and predecessors
(*->u) [the undirected line digraph] and to the two copies of its tail u; copy x^i adjacent to the out-arcs of x.
Z_5 lift: GH-part voltage 0; hops: copy p^i of a point joined to copy (s_k(p))^i of a line in level +t_k (k=1,2).
Bipartite: side A = point copies + arcs leaving lines; side B = line copies + arcs leaving points.
Max degree q+3 (arcs); copies have degree (q+1)/2 + 2."""
import random, subprocess, sys
import gh
SCR = '/tmp/claude-0/-home-user-degree-diameter/0ad899b8-ae47-58b5-b704-0795802a53c1/scratchpad'
q = int(sys.argv[1]); seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
hopmode = sys.argv[3] if len(sys.argv) > 3 else 'both'
H = gh.load(q); N = H.N; V0 = 2 * N
rng = random.Random(seed)
edges = gh.flags(H); rng.shuffle(edges)
nbr_e = [[] for _ in range(V0)]
for k, (u, w) in enumerate(edges):
    nbr_e[u].append((w, k)); nbr_e[w].append((u, k))
for x in nbr_e: rng.shuffle(x)
ptr = [0] * V0; usedE = [False] * len(edges); arcs = []
for s in range(V0):
    if ptr[s] >= len(nbr_e[s]): continue
    stack = [s]; path = []
    while stack:
        v = stack[-1]
        while ptr[v] < len(nbr_e[v]) and usedE[nbr_e[v][ptr[v]][1]]: ptr[v] += 1
        if ptr[v] == len(nbr_e[v]): path.append(stack.pop())
        else:
            w, k = nbr_e[v][ptr[v]]; usedE[k] = True; stack.append(w)
    path.reverse(); arcs += list(zip(path, path[1:]))
A = len(arcs)
# vertex ids in one level: arcs 0..A-1, copies A + 2*x + i
def cid(x, i): return A + 2 * x + i
NB = A + 2 * V0
by_tail = [[] for _ in range(V0)]
for k, (a, b) in enumerate(arcs): by_tail[a].append(k)
E = []
for k, (a, b) in enumerate(arcs):
    for k2 in by_tail[b]:
        E.append((k, k2, 0, 0))          # line digraph edge (successor)
    for i in range(2):
        E.append((k, cid(a, i), 0, 0))    # arc - copy of its tail
s1 = list(range(N)); rng.shuffle(s1); s2 = list(range(N)); rng.shuffle(s2)
for p in range(N):
    if hopmode in ('both', 'c1'):
        E.append((cid(p, 0), cid(N + s1[p], 0), 1, 0))
        E.append((cid(p, 1), cid(N + s2[p], 1), 2, 0))
    if hopmode == 'both':
        E.append((cid(p, 0), cid(N + s2[p], 0), 2, 0))
        E.append((cid(p, 1), cid(N + s1[p], 1), 1, 0))
path = f'{SCR}/ve_q{q}_s{seed}_{hopmode}.txt'
gh.write_base(path, NB, 5, 1, E)
print(f'q={q}: level size {NB} = (q+5)P = {(q + 5) * N}; total {5 * NB}')
for D in (8, 9, 10, 11):
    out = subprocess.run(['./liftdiam', path, str(D), '4'], capture_output=True, text=True).stdout.strip().split('\n')
    print(' ', out[0][:95], '|', out[1])
