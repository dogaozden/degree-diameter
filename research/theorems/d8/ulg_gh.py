"""Line digraph of an Eulerian orientation of the H(q) incidence graph (q odd: (q+1)-regular, out-degree (q+1)/2):
U(L(G)) has #flags vertices, degree q+1.  Print its diameter (liftdiam, trivial group).  Counting note:
DGQ's N/5 = #arcs + 2|GH(q)| for odd q."""
import subprocess, sys, random
import gh
SCR = '/tmp/claude-0/-home-user-degree-diameter/0ad899b8-ae47-58b5-b704-0795802a53c1/scratchpad'
q = int(sys.argv[1]); seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
H = gh.load(q); N = H.N
rng = random.Random(seed)
edges = gh.flags(H)
rng.shuffle(edges)
V = 2 * N
nbr_e = [[] for _ in range(V)]
for k, (u, w) in enumerate(edges):
    nbr_e[u].append((w, k)); nbr_e[w].append((u, k))
for x in nbr_e: rng.shuffle(x)
ptr = [0] * V; usedE = [False] * len(edges); arcs = []
for s in range(V):
    if ptr[s] >= len(nbr_e[s]): continue
    stack = [s]; path = []
    while stack:
        v = stack[-1]
        while ptr[v] < len(nbr_e[v]) and usedE[nbr_e[v][ptr[v]][1]]: ptr[v] += 1
        if ptr[v] == len(nbr_e[v]): path.append(stack.pop())
        else:
            w, k = nbr_e[v][ptr[v]]; usedE[k] = True; stack.append(w)
    path.reverse()
    arcs += list(zip(path, path[1:]))
assert len(arcs) == len(edges)
by_tail = [[] for _ in range(V)]
for k, (a, b) in enumerate(arcs): by_tail[a].append(k)
E2 = [(k, k2) for k, (a, b) in enumerate(arcs) for k2 in by_tail[b]]
path = f'{SCR}/ulg_gh_q{q}.txt'
with open(path, 'w') as fh:
    fh.write(f'{len(arcs)} 1 1 {len(E2)}\n')
    for k, k2 in E2: fh.write(f'{k} {k2} 0 0\n')
for D in (7, 8, 9, 10):
    out = subprocess.run(['./liftdiam', path, str(D), '4'], capture_output=True, text=True).stdout.strip().split('\n')
    print(f'q={q} U(L(G)) {len(arcs)} vertices, degree {q+1}:', out[1])
