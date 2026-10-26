"""Edge list of a salift/salift_s state. Usage: python3 -I best2edges.py GROUPS.txt STATE OUT.edges
GROUPS.txt: gap_export text format ("G N id name" + N rows). STATE: first line "N id p [cost]", then 3p lines "u v a"
(white u < p, black v >= p, voltage a). Lift: vertex (u,g) = u*N + g, edge (u,g) ~ (v, g*a) (salift convention)."""
import sys
gfile, state, out = sys.argv[1], sys.argv[2], sys.argv[3]
lines = open(state).read().split('\n')
N, gid, p = map(int, lines[0].split()[:3])
E = [tuple(map(int, l.split())) for l in lines[1:] if l.strip()]
tok = open(gfile).read().split(); i = 0; T = None
while i < len(tok):
    n_, g_ = int(tok[i + 1]), int(tok[i + 2]); i += 4
    if g_ == gid and n_ == N:
        T = [list(map(int, tok[i + r * N:i + (r + 1) * N])) for r in range(N)]; break
    i += n_ * n_
assert T is not None, "group not found"
edges = set()
for u, v, a in E:
    for g in range(N):
        x, y = u * N + g, v * N + T[g][a]
        edges.add((min(x, y), max(x, y)))
with open(out, 'w') as f:
    f.write(f"{2 * p * N}\n" + ''.join(f"{x} {y}\n" for x, y in sorted(edges)))
print(len(edges), "edges (", 3 * p * N, "if simple )")
