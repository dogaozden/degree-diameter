"""Build the Theorem-B graph S[w,M,sigma] for Q(4,q): old points+lines, one clone per ovoid point (w = 1_O),
one shadow line per chosen line, stand-ins: a non-ovoid point (itself); an ovoid point serves at most two shadows,
first by itself, second by its clone. Writes the apsp edge list (gzip), prints n, max degree.
usage: python3 build.py INST SOLUTION OUT.edges.gz"""
import gzip
import sys
from collections import Counter

inst, solf, outf = sys.argv[1], sys.argv[2], sys.argv[3]
with open(inst) as f:
    N, M, NO = map(int, f.readline().split())
    ov = list(map(int, f.readline().split()))
    lines = [list(map(int, f.readline().split())) for _ in range(M)]
O = set(ov)
q = int(round((NO - 1) ** 0.5))
with open(solf) as f:
    k = int(f.readline())
    sel = [int(f.readline()) for _ in range(k)]
clone = {o: N + i for i, o in enumerate(sorted(ov))}
LB = N + NO
SB = LB + M
n = SB + k
edges = []
through = [[] for _ in range(N)]
for j, L in enumerate(lines):
    for p in L:
        edges.append((p, LB + j))
        through[p].append(j)
for o in ov:
    for j in through[o]:
        edges.append((clone[o], LB + j))
used = Counter()
for e, j in enumerate(sel):
    for p in lines[j]:
        if p in O:
            s = p if used[p] == 0 else clone[p]
        else:
            s = p
        assert used[s] == 0, 'stand-in reused'
        used[s] += 1
        edges.append((s, SB + e))
deg = Counter()
for a, b in edges:
    deg[a] += 1; deg[b] += 1
    assert a != b
assert len(set(edges)) == len(edges)
maxd = max(deg.values())
print(f'q={q} n={n} edges={len(edges)} maxdeg={maxd} (target {q+2})')
with gzip.open(outf, 'wt') as g:
    g.write(f'{n}\n')
    g.write(''.join(f'{a} {b}\n' for a, b in edges))
