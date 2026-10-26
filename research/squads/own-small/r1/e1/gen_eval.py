"""gen_eval.py BASE REPS N [TOP]: eval lines for flift (edge order of BASE). Spanning tree (BFS from 0, flift's rule)
gets voltage 0. First free edge: each Aut-orbit rep (reps file "N R rep..."), the other free edges: all N values.
Usage: python3 -I gen_eval.py BASE REPSFILE  (N read from REPSFILE)."""
import sys
base, repsf = sys.argv[1], sys.argv[2]
L = open(base).read().split('\n')
b, m = map(int, L[0].split()[:2])
E = []
for line in L[1:]:
    p = line.split()
    if len(p) >= 2: E.append((int(p[0]), int(p[1])))
E = E[:m]
rp = open(repsf).read().split()
N, R = int(rp[0]), int(rp[1]); reps = [int(x) for x in rp[2:2 + R]]
dart = {u: [] for u in range(b)}
for i, (u, v) in enumerate(E):
    dart[u].append((v, i)); dart[v].append((u, i))
seen = {0}; tree = set(); q = [0]
while q:
    u = q.pop(0)
    for v, e in dart[u]:
        if v not in seen: seen.add(v); tree.add(e); q.append(v)
free = [i for i in range(m) if i not in tree]
first, rest = free[0], free[1:]
import itertools, sys as _s
out = _s.stdout
for a in reps:
    if a == 0 and '--noid' in sys.argv: continue
    for tup in itertools.product(range(N), repeat=len(rest)):
        v = [0] * m
        v[first] = a
        for e, x in zip(rest, tup): v[e] = x
        out.write(' '.join(map(str, v)) + '\n')
