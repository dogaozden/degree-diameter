# Check of Appendix A of joint.tex, parsed from the paper's own verbatim block.
import re, itertools
from collections import deque
s = open('joint.tex').read()
i = s.index('\\section{The $(7,4)$ example in coordinates}')
blk = s[s.index('\\begin{verbatim}', i) + 16: s.index('\\end{verbatim}', i)]
q = 5
Q = lambda x: (x[0]*x[0] + x[1]*x[2] + x[3]*x[4]) % q
def norm(v):
    for c in v:
        if c % q:
            inv = pow(c, q - 2, q); return tuple(x * inv % q for x in v)
rows = []
for line in blk.strip().split('\n'):
    toks = re.findall(r'\(([0-4:]+)\)(\*?)', line)
    rows.append([(tuple(int(t) for t in pt.split(':')), star == '*') for pt, star in toks])
assert len(rows) == 21 and all(len(r) == 6 for r in rows)
pts = sorted({norm(v) for v in itertools.product(range(q), repeat=5) if any(v) and Q(v) == 0})
assert len(pts) == 156
O = {p for p in pts if (p[4] - 2*p[3]) % q == 0}; assert len(O) == 26
# all lines of Q(4,5)
lines = set()
for a in pts:
    for b in pts:
        if a < b and all(Q([(s*x + t*y) % q for x, y in zip(a, b)]) == 0 for s in range(q) for t in range(q)):
            lines.add(frozenset(norm([(s*x + t*y) % q for x, y in zip(a, b)]) for s in range(q) for t in range(q) if (s, t) != (0, 0)))
lines = list(lines); assert len(lines) == 156
assert all(len(L & O) == 1 for L in lines)
for r in rows:
    S = frozenset(p for p, _ in r); assert S in lines, r
    for p, star in r:
        if star: assert p in O
count = {}
for k, r in enumerate(rows):
    for p, _ in r: count.setdefault(p, []).append(k + 1)
multi = {p: ks for p, ks in count.items() if len(ks) > 1}
print("points on two rows:", multi)
for p, ks in multi.items():
    assert p in O and len(ks) == 2
    starred = [k for k in ks if any(pp == p and st for pp, st in rows[k - 1])]
    assert starred == [max(ks)], (p, ks, starred)
# graph
adj = {}
def add(u, v): adj.setdefault(u, set()).add(v); adj.setdefault(v, set()).add(u)
for j, L in enumerate(lines):
    for p in L:
        add(('p', p), ('l', j))
        if p in O: add(('c', p), ('l', j))
for k, r in enumerate(rows):
    for p, star in r: add(('c' if star else 'p', p), ('s', k))
n = len(adj); md = max(len(v) for v in adj.values())
best = 0
for x in adj:
    d = {x: 0}; dq = deque([x])
    while dq:
        u = dq.popleft()
        for w in adj[u]:
            if w not in d: d[w] = d[u] + 1; dq.append(w)
    assert len(d) == n; best = max(best, max(d.values()))
print("order", n, "max degree", md, "diameter", best)
