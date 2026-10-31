import sys
from collections import Counter
lines = open('aut168.txt').read().split('\n')
n = int(lines[0])
auts = [list(map(int, l.split())) for l in lines[1:] if l.strip()]
ident = list(range(n))
def mul(p, q): return [p[q[x]] for x in range(n)]
def order(p):
    k, q = 1, p
    while q != ident:
        q = mul(p, q); k += 1
    return k
def pw(p, e):
    q = ident
    for _ in range(e): q = mul(p, q)
    return q
ords = [order(p) for p in auts]
g = [auts[i] for i in range(len(auts)) if ords[i] == 7][0]
G = [pw(g, e) for e in range(7)]
Gset = {tuple(x) for x in G}
# r for each order-3 element: s g s^-1 = g^r
res = Counter()
examples = {}
for i, s in enumerate(auts):
    if ords[i] != 3: continue
    sinv = [0]*n
    for x, y in enumerate(s): sinv[y] = x
    c = mul(mul(s, g), sinv)
    r = [e for e in range(7) if tuple(G[e]) == tuple(c)][0]
    fix = sum(1 for x in range(n) if s[x] == x)
    res[(fix, r)] += 1
    examples.setdefault((fix, r), s)
print('(fixed points, r) -> number of order-3 elements:', dict(res))
# also order-2 and order-4, 6 elements normalising g: alpha values
res2 = Counter()
for i, s in enumerate(auts):
    if ords[i] in (2, 4, 6, 12, 14, 21):
        sinv = [0]*n
        for x, y in enumerate(s): sinv[y] = x
        c = mul(mul(s, g), sinv)
        r = [e for e in range(7) if tuple(G[e]) == tuple(c)]
        fix = sum(1 for x in range(n) if s[x] == x)
        res2[(ords[i], fix, r[0] if r else None)] += 1
print('other orders (order, fixed points, r):', dict(res2))
import pickle
pickle.dump({'g': g, 'examples': examples}, open('f21_examples.pkl', 'wb'))
