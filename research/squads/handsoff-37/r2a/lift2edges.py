# Usage: lift2edges.py GROUPS.tab SOL > out.edges   (SOL from salift: "N gid p" then 3p lines "u v a")
# Vertex (u,g) = u*N+g; base edge (u,v,a) gives (u,g) ~ (v, g*a) (salift convention). n = 2pN.
import sys
def read_group(path, gid):
    tok = open(path).read().split(); i = 0
    while i < len(tok):
        N, g = int(tok[i + 1]), int(tok[i + 2]); i += 4
        if g == gid: return N, [list(map(int, tok[i + r * N:i + (r + 1) * N])) for r in range(N)]
        i += N * N
    raise SystemExit("group not found")
lines = open(sys.argv[2]).read().split('\n')
N0, gid, p = map(int, lines[0].split())
N, mul = read_group(sys.argv[1], gid)
assert N == N0
edges = [tuple(map(int, l.split())) for l in lines[1:] if l.strip()]
out = [str(2 * p * N)]
for u, v, a in edges:
    for g in range(N):
        out.append(f"{u * N + g} {v * N + mul[g][a]}")
print('\n'.join(out))
