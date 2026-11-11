"""omegalab.py (referee omega-dq): Omega B_1 with a separate labelling of every copy (the table-audit-2 repair, not the
thesis), wired from Figs 2.21a/b by my own reading, written as an edge list for an all-pairs checker.
  copy c = 5B + i holds base vertex v at id c*2n + v (points 0..n-1, lines n..2n-1), with the base edges;
  row t of copy c is the pair (point P_c[t], line L_c[t]) read from LAB (first C*n numbers: P_c, then C*n: L_c);
  in block B the inner dot is the line if INNER[B] == 'L', else the point; the outer dot is the other one;
  K(t,k) and K(t,kbar) at ids 2nC + (5*bar + k)*n + t;
  type a: K(t,k) on inner dots of copies k-1, k+1; K(t,kbar) on outer dots of copies k+2, k+3;
  type b: K(t,k) on outer dots of copies k+3, k+4; K(t,kbar) on inner dots of copies k-1, k+1.
usage: python3 -I omegalab.py hex.txt TYPES INNER LAB out.txt"""
import sys
hexp, types, inner, labp, outp = sys.argv[1:6]
with open(hexp) as f:
    nb = int(f.readline())
    base = [tuple(map(int, l.split())) for l in f if l.strip()]
n = nb // 2
C = 5 * len(types)
vals = list(map(int, open(labp).read().split()))
assert len(vals) == 2 * C * n, (len(vals), 2 * C * n)
P = [vals[c * n:(c + 1) * n] for c in range(C)]
L = [vals[C * n + c * n:C * n + (c + 1) * n] for c in range(C)]
for c in range(C):
    assert sorted(P[c]) == list(range(n)) and sorted(L[c]) == list(range(n))
K0 = 2 * n * C
edges = []
for c in range(C):
    for u, v in base:
        edges.append((c * nb + u, c * nb + v))


def dot(c, t, side):                      # side 'in' or 'out'
    line_inner = inner[c // 5] == 'L'
    use_line = (side == 'in') == line_inner
    return c * nb + (n + L[c][t] if use_line else P[c][t])


for B, ty in enumerate(types):
    for t in range(n):
        for k in range(5):
            if ty == 'a':
                plan = [(0, (k - 1) % 5, 'in'), (0, (k + 1) % 5, 'in'), (1, (k + 2) % 5, 'out'), (1, (k + 3) % 5, 'out')]
            else:
                plan = [(0, (k + 3) % 5, 'out'), (0, (k + 4) % 5, 'out'), (1, (k - 1) % 5, 'in'), (1, (k + 1) % 5, 'in')]
            for bar, i, side in plan:
                edges.append((K0 + (5 * bar + k) * n + t, dot(5 * B + i, t, side)))
with open(outp, 'w') as f:
    f.write(f"{K0 + 10 * n}\n")
    for u, v in edges:
        f.write(f"{u} {v}\n")
print(f"vertices {K0 + 10 * n}, edges {len(edges)}")
