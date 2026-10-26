# sol2edges.py GROUPS.txt SOL > edges : salift .sol ("N id p" then "u v a" lines) to an edge list.
# vertex (u,g) = u*N+g (u < p white, u >= p black), edge (u,g) ~ (v, g*a); group mult table from gap_export text.
import sys
groups, solf = sys.argv[1], sys.argv[2]
tok = open(groups).read().split()
lines = open(solf).read().split("\n")
N, gid, p = map(int, lines[0].split())
i = 0
mul = None
while i < len(tok):
    n_, g_, nm = int(tok[i+1]), int(tok[i+2]), tok[i+3]
    i += 4
    tab = tok[i:i+n_*n_]; i += n_*n_
    if n_ == N and g_ == gid:
        mul = [int(x) for x in tab]; break
assert mul is not None, "group not found"
edges = set()
for ln in lines[1:]:
    if not ln.strip(): continue
    u, v, a = map(int, ln.split())
    for g in range(N):
        x = u*N + g; y = v*N + mul[g*N + a]
        edges.add((min(x, y), max(x, y)))
print(2*p*N)
for x, y in sorted(edges):
    print(x, y)
