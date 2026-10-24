"""Write a self-contained builder (stdlib only) for a route-chart lift whose controller is a Haar graph of a metacyclic
group Z_M x|_t Z_N (elements (x, y), (x1, y1)(x2, y2) = (x1 + t^y1 x2 mod M, y1 + y2 mod N); groups.py index x*N + y).
usage: python3 r3/make_haar_builder.py VOLT CHART.txt q M N t out.py "description"
VOLT: ctrl_search .volt of a 1+1 base (k parallel edges a0 b0 with colours 0..k-1)."""
import sys
sys.path.insert(0, '.')
from gf import GF
voltp, chartp, q, M, Nn, t, outp, desc = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6]), sys.argv[7], sys.argv[8]
rows = [list(map(int, l.split())) for l in open(voltp) if l.strip()]
r, k, g = rows[0]; assert r == 1 and g == M * Nn
S = [None] * k
for (i, j, c, v) in rows[1:]: S[c] = (v // Nn, v % Nn)
vals = [list(map(int, l.split())) for l in open(chartp) if l.strip()]
A = [[v[4 * s:4 * s + 4] for s in range(4)] for v in vals[:k]]; b = [v for v in vals[k:2 * k]]
F = GF(q); Q = q ** 4; n = 2 * g * Q
src = f'''#!/usr/bin/env python3
"""{desc}
Self-contained (stdlib only).  Route-chart lift (research/theorems/CHART_LIFTS.md) of a Haar graph:
  * group G = Z_{M} x|_{t} Z_{Nn}: elements (x, y), (x1, y1)(x2, y2) = (x1 + {t}^y1 x2 mod {M}, y1 + y2 mod {Nn}); order {g};
  * controller: Haar graph, a_g ~ b_(s g) for s = S[c], edge colour c (c = 0..{k - 1}); {g} vertices per side;
  * fibre F_{q}^4; controller edge of colour c lifts to (a_g, u) ~ (b_(s g), A_c u + lam B_c), lam in F_{q}.
Degree {k} x {q} = {k * q}; order 2 * {g} * {Q} = {n}.
Vertex numbering: (a_g, u) -> idx(g)*{Q} + id(u), (b_h, u) -> {g * Q} + idx(h)*{Q} + id(u), idx(x, y) = x*{Nn} + y,
id(u) = sum u_i {q}^i.  F_{q} elements are 0..{q - 1} with the tables below.
usage: python3 THIS out.edges   (apsp.c format: first line n, then one edge "u v" per line)"""
import sys, itertools
ADD = {F.add!r}
MUL = {F.mul!r}
M, N, t = {M}, {Nn}, {t}
S = {S!r}   # S[c] = (x, y), the voltage of colour c
A = {A!r}
B = {b!r}
q = {q}; Q = q ** 4

def gmul(a, b): return ((a[0] + pow(t, a[1], M) * b[0]) % M, (a[1] + b[1]) % N)
def idx(a): return a[0] * N + a[1]

def mat_vec(Mx, v):
    out = []
    for row in Mx:
        s = 0
        for a, x in zip(row, v): s = ADD[s][MUL[a][x]]
        out.append(s)
    return out

def vid(v): return sum(c * q ** i for i, c in enumerate(v))

def build():
    G = [(x, y) for x in range(M) for y in range(N)]; nA = len(G) * Q; E = []
    vecs = list(itertools.product(range(q), repeat=4))
    for c, s in enumerate(S):
        for g in G:
            a, h = idx(g), idx(gmul(s, g))
            for u in vecs:
                y0 = mat_vec(A[c], u)
                for lam in range(q):
                    y = [ADD[p][MUL[lam][w]] for p, w in zip(y0, B[c])]
                    E.append((a * Q + vid(u), nA + h * Q + vid(y)))
    assert len(set(E)) == len(E), 'repeated edge'
    return 2 * nA, E

if __name__ == '__main__':
    n, E = build()
    with open(sys.argv[1], 'w') as f:
        f.write(f"{{n}}\\n"); f.writelines(f"{{a}} {{b}}\\n" for a, b in E)
    print('vertices', n, 'edges', len(E))
'''
open(outp, 'w').write(src)
print('wrote', outp, 'n =', n, 'S =', S)
