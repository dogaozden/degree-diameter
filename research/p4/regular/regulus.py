"""Regulus switching in the Hermitian spread of H(q): which S-reguli can be traded for point centres?

Pi: x0 + c x4 = 0 (-c a non-square); S = hexagon lines inside Pi (a Hermitian spread). For a point P off Pi its
shadow is {m meet Pi : m a hexagon line through P}. Prints: shadow collinearity, groups of shadows meeting the same
q+1 S-lines (an opposite regulus when the group has q+1 members and covers those lines), and whether the centres
of one group are pairwise opposite (distance 6 in the incidence graph).
python3 regulus.py q
"""
import json
import sys
from collections import defaultdict, deque
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
q = int(sys.argv[1])
d = json.loads((ROOT / 'research' / 'gh6' / 'hex' / f'hexagon_q{q}.json').read_text())
sys.path.insert(0, str(ROOT / 'research' / 'gh6'))
import gh_build  # noqa: E402
pts, lines = gh_build.quadric_points(q), d['lines']
N = len(lines)
assert all((p[0] * p[4] + p[1] * p[5] + p[2] * p[6] - p[3] * p[3]) % q == 0 for p in pts)
sq = {x * x % q for x in range(1, q)}
c = next(c for c in range(1, q) if (-c) % q not in sq)
inPi = [(p[0] + c * p[4]) % q == 0 for p in pts]
through = [[] for _ in range(N)]
for k, L in enumerate(lines):
    for p in L:
        through[p].append(k)
S = [k for k, L in enumerate(lines) if all(inPi[p] for p in L)]
Sof = {}
for k in S:
    for p in lines[k]:
        Sof[p] = k
print('q', q, 'c', c, 'Pi points', sum(inPi), 'S lines', len(S), 'covered', len(Sof))


def rank(vs):
    M = [list(v) for v in vs]
    r = 0
    for col in range(7):
        piv = next((i for i in range(r, len(M)) if M[i][col] % q), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        iv = pow(M[r][col], q - 2, q)
        M[r] = [x * iv % q for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][col] % q:
                f = M[i][col]
                M[i] = [(a - f * b) % q for a, b in zip(M[i], M[r])]
        r += 1
    return r


shadow = {}
for P in range(N):
    if inPi[P]:
        continue
    sh = []
    for k in through[P]:
        x = [p for p in lines[k] if inPi[p]]
        assert len(x) == 1
        sh.append(x[0])
    shadow[P] = tuple(sorted(sh))
coll = sum(rank([pts[x] for x in sh]) == 2 for sh in shadow.values())
print('off-Pi points', len(shadow), 'collinear shadows', coll, 'distinct shadows', len(set(shadow.values())))
groups = defaultdict(list)
for P, sh in shadow.items():
    groups[tuple(sorted({Sof[x] for x in sh}))].append(P)
sizes = defaultdict(int)
for key, Ps in groups.items():
    sizes[(len(key), len(Ps))] += 1
print('groups (#S-lines met, #centres): count', dict(sizes))
adj = [[N + k for k in through[p]] for p in range(N)] + [list(L) for L in lines]


def dist_from(s):
    dist = [-1] * (2 * N)
    dist[s] = 0
    dq = deque([s])
    while dq:
        u = dq.popleft()
        for w in adj[u]:
            if dist[w] < 0:
                dist[w] = dist[u] + 1
                dq.append(w)
    return dist


regs = [(key, Ps) for key, Ps in groups.items() if len(Ps) == q + 1 and len(key) == q + 1]
good = []
for key, Ps in regs:
    cover = sorted(x for P in Ps for x in shadow[P])
    full = sorted(p for k in key for p in lines[k])
    dd = dist_from(Ps[0])
    opp = all(dist_from(P1)[P2] == 6 for i, P1 in enumerate(Ps) for P2 in Ps[i + 1:])
    if cover == full:
        good.append((key, Ps, opp))
print('switchable reguli (shadows partition the q+1 S-lines):', len(good), 'with centres pairwise opposite:',
      sum(g[2] for g in good))
out = Path(__file__).resolve().parent / f'reguli_q{q}.json'
out.write_text(json.dumps({'q': q, 'c': c, 'S': S, 'reguli': [[list(k), Ps, o] for k, Ps, o in good]}))
print('wrote', out)
