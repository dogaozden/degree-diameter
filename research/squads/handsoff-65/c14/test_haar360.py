import sys
tok = open('g360/sg_360_53.txt').read().split(); m = int(tok[0])
mul = [list(map(int, tok[1 + i*m:1 + (i+1)*m])) for i in range(m)]
inv = [r.index(0) for r in mul]
tk = open('../c6/h360_53.edges').read().split(); n = int(tk[0]); E = [(int(tk[1+2*k]), int(tk[2+2*k])) for k in range((len(tk)-1)//2)]
h = n // 2
nb = [set() for _ in range(n)]
for u, v in E:
    nb[u].add(v - h); nb[v].add(u - h) if v >= h else None
    if u >= h: nb[u].add(v); nb[v].add(u)  # fix below
nb = [set() for _ in range(n)]
for u, v in E:
    a, b = (u, v) if u < h else (v, u)
    nb[a].add(b - h); nb[b].add(a)  # store B index for A side; A index for B side
S = sorted(nb[0]); print("S", S, "deg", len(S))
tests = {
 'left mul s*i': lambda s, i: mul[s][i],
 'right mul i*s': lambda s, i: mul[i][s],
 'left inv s^-1*i': lambda s, i: mul[inv[s]][i],
 'right i*s^-1': lambda s, i: mul[i][inv[s]],
}
for name, f in tests.items():
    ok = all(set(f(s, i) for s in S) == nb[i] for i in range(h))
    ok2 = all(set(f(s, i) for s in S) == nb[i] for i in range(h))
    cnt = sum(1 for i in range(h) if set(f(s, i) for s in S) == nb[i])
    print(name, "matches", cnt, "of", h)
