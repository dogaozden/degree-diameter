"""Z7 quotient of conder168 (C168.1) in lift.c INIT format (N=7 k=12).
usage: quot7.py OUTSTATE  -> also prints checks. Lift vertex (u,g) = u*7+g (white u), (k+v)*7+g (black v), edge (u,g)~(v,g+a)."""
import sys
from collections import deque
R = '/home/user/degree-diameter/research/squads/handsoff-37/'
toks = open(R + 'shared/seeds/conder168.edges').read().split()
n = int(toks[0])
E0 = set()
for i in range(1, len(toks), 2):
    a, b = int(toks[i]), int(toks[i + 1]); E0.add((min(a, b), max(a, b)))
N = [[] for _ in range(n)]
for a, b in E0:
    N[a].append(b); N[b].append(a)
lines = open(R + 'c5/out/aut168.txt').read().split('\n')
auts = [list(map(int, l.split())) for l in lines[1:] if l.strip()]
def order(p):
    k = 1; q = p[:]
    while q != list(range(n)):
        q = [p[x] for x in q]; k += 1
    return k
sig = None
for p in auts:
    if order(p) == 7:
        sig = p; break
assert sig is not None
# colour classes
col = [-1] * n; col[0] = 0; dq = deque([0])
while dq:
    x = dq.popleft()
    for y in N[x]:
        if col[y] < 0: col[y] = 1 - col[x]; dq.append(y)
# orbits of sig: rep and index (orbit j, power i)
orb = [-1] * n; pw = [0] * n; reps = []
for v in range(n):
    if orb[v] >= 0: continue
    j = len(reps); reps.append(v)
    x = v; i = 0
    while orb[x] < 0:
        orb[x] = j; pw[x] = i; x = sig[x]; i += 1
assert len(reps) == 24, len(reps)
Ar = [r for r in reps if col[r] == 0]; Br = [r for r in reps if col[r] == 1]
assert len(Ar) == 12 and len(Br) == 12
Ai = {r: i for i, r in enumerate(Ar)}; Bi = {r: i for i, r in enumerate(Br)}
edges = set()
for r in Ar:
    u = Ai[r]
    for w in N[r]:
        v = Bi[reps[orb[w]]]
        # w = sig^{pw[w]}(rep_v): voltage a = pw[w] (since sig^g(r) ~ sig^{g+a}(rep_v))
        edges.add((u, v, pw[w]))
edges = sorted(edges)
assert len(edges) == 36, len(edges)
# check: lift reproduces conder168 exactly
def lift_id(side, j, g):
    return (j * 7 + g) if side == 0 else None
lifted = set()
Vid = {}
for (u, v, a) in edges:
    for g in range(7):
        x = u * 7 + g; y = (12 + v) * 7 + (g + a) % 7
        # map quotient vertex ids to conder ids: white orbit u power g -> sig^g(Ar[u])
        pass
def conder_of(vid):
    if vid < 84:
        u, g = divmod(vid, 7); r = Ar[u]
    else:
        v, g = divmod(vid - 84, 7); r = Br[v]
    x = r
    for _ in range(g): x = sig[x]
    return x
ok = True
G = set()
for (u, v, a) in edges:
    for g in range(7):
        x = u * 7 + g; y = (12 + v) * 7 + (g + a) % 7
        cx, cy = conder_of(x), conder_of(y)
        G.add((min(cx, cy), max(cx, cy)))
print('lift reproduces conder168:', G == E0, 'edges', len(G), len(E0))
with open(sys.argv[1], 'w') as f:
    f.write('7 12\n')
    for (u, v, a) in edges: f.write('%d %d %d\n' % (u, v, a))
print('wrote', sys.argv[1], 'sig order 7; base edges', len(edges))
