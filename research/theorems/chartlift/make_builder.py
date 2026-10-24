"""Write a self-contained builder (stdlib only) for a route-chart lift of a voltage-lift controller.
usage: python3 make_builder.py VOLT CHART.txt q GROUP out.py "description"
VOLT: ctrl_search .volt file (r k g, then lines "i j colour voltage"); GROUP: cyclic:N or a gtab table file."""
import sys
from gf import GF
voltp, chartp, q, group, outp, desc = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4], sys.argv[5], sys.argv[6]
rows = [list(map(int, l.split())) for l in open(voltp) if l.strip()]
r, k, g = rows[0]; base = [tuple(x) for x in rows[1:]]
vals = [list(map(int, l.split())) for l in open(chartp) if l.strip()]
A = [[v[4 * t:4 * t + 4] for t in range(4)] for v in vals[:k]]; b = [v for v in vals[k:2 * k]]
F = GF(q)
if group.startswith('cyclic:'):
    N = int(group[7:]); assert N == g
    gcode = "G = %d\ndef gmul(a, x): return (a + x) %% G            # Z_%d, written additively\n" % (N, N)
else:
    T = [list(map(int, l.split())) for l in open(group).read().split('\n')[1:] if l.strip()][0]
    gcode = "G = %d\nT = %r\ndef gmul(a, x): return T[a * G + x]\n" % (g, T)
m = r * g; Q = q ** 4; n = 2 * m * Q
src = f'''#!/usr/bin/env python3
"""{desc}
Self-contained (stdlib only).  Route-chart lift (CHART_LIFTS.md):
  * base: {k}-regular bipartite multigraph on {r} + {r} vertices; base edge (a_i, b_j, colour c, voltage v);
  * controller: voltage lift by a group of order {g}: (a_i, x) ~ (b_j, v * x); m = {m} vertices per side;
  * fibre F_{q}^4; controller edge of colour c lifts to ((a_i, x), u) ~ ((b_j, v*x), A_c u + lam b_c), lam in F_{q}.
Degree {k} x {q} = {k * q}; order 2 * {m} * {Q} = {n}.
F_{q} elements are 0..{q - 1} with the tables below.  Vertex numbering: A-vertex ((a_i, x), u) -> (i*G + x)*{Q} + id(u);
B-vertex ((b_j, y), u) -> {m * Q} + (j*G + y)*{Q} + id(u); id(u) = sum u_t {q}^t.
usage: python3 THIS out.edges   (apsp.c format: first line n, then one edge "u v" per line)"""
import sys, itertools
ADD = {F.add!r}
MUL = {F.mul!r}
{gcode}BASE = {base!r}   # (i, j, colour, voltage)
A = {A!r}
B = {b!r}
q = {q}; Q = q ** 4; R = {r}

def mat_vec(M, v):
    out = []
    for row in M:
        s = 0
        for a, x in zip(row, v): s = ADD[s][MUL[a][x]]
        out.append(s)
    return out

def vid(v): return sum(c * q ** t for t, c in enumerate(v))

def build():
    m = R * G; nA = m * Q; E = []
    vecs = list(itertools.product(range(q), repeat=4))
    for (i, j, c, v) in BASE:
        for x in range(G):
            a, bb = i * G + x, j * G + gmul(v, x)
            for u in vecs:
                y0 = mat_vec(A[c], u)
                for lam in range(q):
                    y = [ADD[p][MUL[lam][t]] for p, t in zip(y0, B[c])]
                    E.append((a * Q + vid(u), nA + bb * Q + vid(y)))
    assert len(set(E)) == len(E), 'repeated edge'
    return 2 * nA, E

if __name__ == '__main__':
    n, E = build()
    with open(sys.argv[1], 'w') as f:
        f.write(f"{{n}}\\n"); f.writelines(f"{{a}} {{b}}\\n" for a, b in E)
    print('vertices', n, 'edges', len(E))
'''
open(outp, 'w').write(src)
print('wrote', outp, 'n =', n)
