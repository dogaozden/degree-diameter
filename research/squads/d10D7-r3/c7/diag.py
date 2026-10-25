import sys, os, subprocess, collections
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen import *
from exp import check, HERE
exp = sys.argv[1]; seed = int(sys.argv[2])
N, LP = load_hex(5)
rng = np.random.default_rng(seed)
M = rng.permutation(N)
touched = set()
if exp == 'hub1':
    p = int(rng.integers(N)); l = int(M[p])
    dl = [(p, i) for i in range(3)]
    Z, Zp = 6 * N, 6 * N + 1
    new = [(Z, i * 2 * N + p) for i in range(3)] + [(Zp, i * 2 * N + N + l) for i in range(3)]
    n, E = build(N, LP, M, dl, new, 2)
    touched |= {Z, Zp}
elif exp == 'cl8':
    ps = rng.choice(N * 3, 4, replace=False)
    dl = [(int(x) % N, int(x) // N) for x in ps]
    ends = []
    for (p, i) in dl:
        ends.append(i * 2 * N + p); ends.append(((i + 1) % 3) * 2 * N + N + int(M[p]))
    match = {(0, 2), (1, 4), (3, 6), (5, 7)}
    new = []
    for j in range(8):
        new.append((6 * N + j, ends[j])); touched.add(6 * N + j)
        for k in range(j + 1, 8):
            if (j, k) not in match: new.append((6 * N + j, 6 * N + k))
    n, E = build(N, LP, M, dl, new, 8)
touched |= set(ends) if exp == 'cl8' else {p + i * 2 * N for (p, i) in dl} | {int(M[p]) + ((i + 1) % 3) * 2 * N + N for (p, i) in dl}
fn = os.path.join(HERE, 'diag_%s.edges' % exp); write(n, E, fn)
out = subprocess.run([os.path.join(HERE, 'viol'), fn, '7', 'list'], capture_output=True, text=True).stdout.splitlines()
srcs = [int(l.split()[1]) for l in out if l.startswith('SRC')]
print(out[-1] if out else '')
# multi-source BFS distance from touched set in modified graph
adj = [[] for _ in range(n)]
for (u, v) in E: adj[u].append(v); adj[v].append(u)
dist = {t: 0 for t in touched}; fr = list(touched)
while fr:
    nf = []
    for x in fr:
        for y in adj[x]:
            if y not in dist: dist[y] = dist[x] + 1; nf.append(y)
    fr = nf
hist = collections.Counter(min(dist.get(s, 99), 99) for s in srcs)
print('violating sources', len(srcs), 'distance-from-modification histogram', sorted(hist.items()))
# which kind of vertex are the violating sources
kind = collections.Counter(('new' if s >= 6*N else ('point' if (s % (2*N)) < N else 'line')) for s in srcs)
print('kinds', dict(kind))
os.remove(fn)
