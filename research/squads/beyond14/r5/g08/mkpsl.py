#!/usr/bin/env python3
"""mkpsl.py q OUT: multiplication table of PSL(2,q) (q prime) in the own-small format, identity = index 0, id 1."""
import sys, random
q = int(sys.argv[1]); out = sys.argv[2]
def canon(M):
    a, b, c, d = M
    t1 = (a, b, c, d); t2 = ((-a) % q, (-b) % q, (-c) % q, (-d) % q)
    return min(t1, t2)
els = set()
for a in range(q):
    for b in range(q):
        for c in range(q):
            for d in range(q):
                if (a * d - b * c) % q == 1: els.add(canon((a, b, c, d)))
els = sorted(els, key=lambda t: (t != canon((1, 0, 0, 1)), t))
N = len(els); idx = {e: i for i, e in enumerate(els)}
def mul(x, y):
    a, b, c, d = x; e, f, g, h = y
    return canon(((a * e + b * g) % q, (a * f + b * h) % q, (c * e + d * g) % q, (c * f + d * h) % q))
T = [[idx[mul(els[x], els[y])] for y in range(N)] for x in range(N)]
rnd = random.Random(1)
for _ in range(20000):
    a, b, c = rnd.randrange(N), rnd.randrange(N), rnd.randrange(N)
    assert T[T[a][b]][c] == T[a][T[b][c]]
with open(out, 'w') as f:
    f.write(f"G {N} 1 PSL2_{q}\n")
    for row in T: f.write(" ".join(map(str, row)) + "\n")
print("N =", N)
