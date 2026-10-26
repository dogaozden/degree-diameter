"""explode.py: expand a glift base file (D n lift) into an explicit edge list for gcheck (card c8)."""
import sys
lines = open(sys.argv[1]).read().split('\n')
gt, n = lines[0].split(); n = int(n)
V = int(lines[1]); cols = list(map(int, lines[2].split()))
darts = [tuple(map(int, l.split())) for l in lines[3:] if l.strip()]
G = 2 * n
def idx(v, g): return v * G + g
def el(a):  # group element encoding: a = k + n*t
    return a % n, a // n
def mul(g, a):  # (k,t)*(k',t') = (k + (-1)^t k', t+t')
    k, t = divmod(g, n) if False else (g % n, g // n)
    k2, t2 = el(a)
    return ((k + (k2 if t == 0 else -k2)) % n) + n * ((t + t2) % 2)
edges = []
for (u, v, a) in darts:
    for g in range(G):
        edges.append((idx(u, g), idx(v, mul(g, a))))
seen = set(); out = []
for x, y in edges:
    key = (min(x, y), max(x, y), x == y)
    # semi-edges give one edge per lift vertex: keep each undirected edge once
    e = (min(x, y), max(x, y))
    if x == y:
        out.append(e); continue
    if e in seen:
        continue
    seen.add(e); out.append(e)
with open(sys.argv[2], 'w') as f:
    f.write(f'{V*G}\n')
    for x, y in out:
        f.write(f'{x} {y}\n')
print('vertices', V*G, 'edges', len(out), file=sys.stderr)
