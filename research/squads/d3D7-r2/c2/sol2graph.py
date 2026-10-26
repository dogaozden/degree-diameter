import sys
# usage: sol2graph.py SOL GROUPS GID > out.edges   (vertex (u,g) = u*N+g; base edge (u,v,a): (u,g) ~ (v, g*a))
sol, gfile, gid = sys.argv[1], sys.argv[2], int(sys.argv[3])
lines = [l for l in open(sol).read().split('\n') if l.strip()]
N, _, p = map(int, lines[0].split())
toks = open(gfile).read().split()
i = 0; mul = None
while i < len(toks):
    if toks[i] == 'G' and int(toks[i+1]) == N and int(toks[i+2]) == gid:
        mul = list(map(int, toks[i+4:i+4+N*N])); break
    i += 4 + N*N
if mul is None: raise SystemExit('group not found')
E = [tuple(map(int, l.split())) for l in lines[1:]]
out = [str(2*p*N)]
for u, v, a in E:
    for g in range(N):
        out.append(f"{u*N+g} {v*N+mul[g*N+a]}")
print('\n'.join(out))
