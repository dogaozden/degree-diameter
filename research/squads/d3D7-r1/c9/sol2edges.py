import sys
# usage: sol2edges.py SOL GROUPS > out.edges   (vertex (u,g) = u*N+g; base edge (u,v,a): (u,g) ~ (v, g*a); whites u<p)
sol, gfile = sys.argv[1], sys.argv[2]
lines = open(sol).read().split('\n')
N, _, p = map(int, lines[0].split()); gid = int(sys.argv[3])
toks = open(gfile).read().split()
i = 0
while True:
    if toks[i] == 'G' and int(toks[i+1]) == N and int(toks[i+2]) == gid:
        mul = list(map(int, toks[i+4:i+4+N*N])); break
    i += 1
    if i >= len(toks): raise SystemExit('group not found')
    # skip a whole block: 'G N id name' + N*N entries
    if toks[i-1] == 'G':
        pass
E = []
for ln in lines[1:]:
    if ln.strip():
        u, v, a = map(int, ln.split()); E.append((u, v, a))
n = 2 * p * N
out = [str(n)]
for u, v, a in E:
    for g in range(N):
        out.append(f"{u*N+g} {v*N+mul[g*N+a]}")
print('\n'.join(out))
