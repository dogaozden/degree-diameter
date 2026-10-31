"""Find F21 = <g, s> inside Aut(C168.1): g order 7, s order 3 with s g s^-1 = g^r (r of order 3 mod 7)."""
import sys
from collections import Counter
lines = open(sys.argv[1]).read().split('\n')
n = int(lines[0])
auts = [list(map(int, l.split())) for l in lines[1:] if l.strip()]
ident = list(range(n))
def mul(p, q):  # (p*q)(x) = p(q(x))
    return [p[q[x]] for x in range(n)]
def order(p):
    k, q = 1, p
    while q != ident:
        q = mul(p, q); k += 1
    return k
def cyc(p):
    seen = [False]*n; cs = []
    for i in range(n):
        if not seen[i]:
            L = 0; j = i
            while not seen[j]:
                seen[j] = True; j = p[j]; L += 1
            cs.append(L)
    return cs
def inv(p):
    q = [0]*n
    for i, x in enumerate(p): q[x] = i
    return q
ords = {}
for idx, p in enumerate(auts):
    ords[idx] = order(p)
print('auts', len(auts), 'orders', Counter(ords.values()))
key = {tuple(p): i for i, p in enumerate(auts)}
g7 = [i for i in ords if ords[i] == 7]
s3 = [i for i in ords if ords[i] == 3]
print('order-7 elements', len(g7), 'order-3 elements', len(s3))
# power structure of order-7 elements
def pw(p, e):
    q = ident
    for _ in range(e): q = mul(p, q)
    return q
# candidate pairs: s normalises <g>
found = []
for gi in g7:
    g = auts[gi]
    G = {tuple(pw(g, e)) for e in range(7)}
    for si in s3:
        s = auts[si]
        si_inv = inv(s)
        conj = mul(mul(s, g), si_inv)
        if tuple(conj) in G:
            fix = sum(1 for x in range(n) if s[x] == x)
            found.append((gi, si, fix, cyc(g).count(1)))
print('pairs (g,s) with s normalising <g>:', len(found))
print('fix counts of normalising s:', Counter(f[2] for f in found))
print('fixed points of g (should be 0):', Counter(f[3] for f in found))
# which order-7 elements have normalizing order-3 elements
print('distinct <g> with normaliser order-3 elem:', len({tuple(pw(auts[f[0]],e)) for f in found for e in range(7)}) // 6)
# s fixes which vertices
for gi, si, fix, _ in found[:3]:
    s = auts[si]
    print('example s fixed points:', [x for x in range(n) if s[x] == x])
