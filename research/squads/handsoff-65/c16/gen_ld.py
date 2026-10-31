# usage: python3 -I gen_ld.py q OUT   -- D(3,q), prime q: points (p1,p2,p3), lines [l1,l2,l3],
# incidence l2 + p2 = p1*l1, l3 + p3 = p1*l2 (mod q). Writes edge list: n, then "u v" (points 0..q^3-1, lines q^3..)
import sys
q = int(sys.argv[1]); out = sys.argv[2]
N = q**3
def idx(a, b, c): return (a * q + b) * q + c
edges = []
for p1 in range(q):
    for p2 in range(q):
        for p3 in range(q):
            P = idx(p1, p2, p3)
            for l1 in range(q):
                l2 = (p1 * l1 - p2) % q
                l3 = (p1 * l2 - p3) % q
                edges.append((P, N + idx(l1, l2, l3)))
with open(out, 'w') as f:
    f.write(f"{2*N}\n")
    for u, v in edges:
        f.write(f"{u} {v}\n")
print("wrote", out, "n", 2*N, "edges", len(edges))
