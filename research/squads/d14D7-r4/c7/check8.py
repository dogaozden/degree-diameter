# check8.py: (1) BFS check on H(8): dist_incidence(x,y) <= 4 iff B(x,y) = 0 (sampled sources);
# (2) elliptic hyperplane sections X4 = c*X0 + d*X3 with c*T^2 + d*T + 1 irreducible: points, hexagon lines inside,
#     spread test (each point of the section on exactly one such line), orthogonality degree inside the section.
import sys, random, collections
def gmul(a, b):
    r = 0
    for i in range(3):
        if (b >> i) & 1: r ^= a << i
    for bit in (4, 3):
        if (r >> bit) & 1: r ^= 0xB << (bit - 3)
    return r
MUL = [[gmul(a, b) for b in range(8)] for a in range(8)]
f = open('GH8'); P, q = map(int, f.readline().split())
lines = [list(map(int, f.readline().split())) for _ in range(P)]
X = [tuple(map(int, l.split())) for l in open('coords8.txt')]
assert len(X) == P and all(len(l) == q + 1 for l in lines)
def B(x, y):
    return MUL[x[0]][y[4]] ^ MUL[x[4]][y[0]] ^ MUL[x[1]][y[5]] ^ MUL[x[5]][y[1]] ^ MUL[x[2]][y[6]] ^ MUL[x[6]][y[2]]
# (1) incidence BFS
pl = [[] for _ in range(P)]
for li, l in enumerate(lines):
    for p in l: pl[p].append(P + li)
adj = [[] for _ in range(2 * P)]
for li, l in enumerate(lines):
    for p in l: adj[p].append(P + li); adj[P + li].append(p)
def bfs(s):
    d = [-1] * (2 * P); d[s] = 0; dq = collections.deque([s])
    while dq:
        x = dq.popleft()
        for y in adj[x]:
            if d[y] < 0: d[y] = d[x] + 1; dq.append(y)
    return d
random.seed(1); bad = 0; srcs = [0, 1, P - 1] + random.sample(range(P), 3)
for s in srcs:
    d = bfs(s)
    for y in range(P):
        close = d[y] <= 4
        if close != (B(X[s], X[y]) == 0): bad += 1
    print("source", s, "checked; mismatches so far", bad, flush=True)
print("BFS check dist<=4 iff B=0: mismatches =", bad, "(sources:", srcs, ")")
# (2) elliptic sections
good = []
for c in range(1, 8):
    for d in range(1, 8):
        if all((MUL[c][MUL[T][T]] ^ MUL[d][T] ^ 1) != 0 for T in range(8)):
            good.append((c, d))
print("(c,d) with c*T^2+d*T+1 irreducible over GF(8):", good)
for (c, d) in good:
    E = [i for i in range(P) if X[i][4] == (MUL[c][X[i][0]] ^ MUL[d][X[i][3]])]
    inE = set(E)
    spread = [l for l in lines if all(p in inE for p in l)]
    cover = collections.Counter(p for l in spread for p in l)
    ok = len(E) == 4617 and len(spread) == 513 and len(cover) == len(E) and all(v == 1 for v in cover.values())
    deg = sum(1 for y in E if y != E[0] and B(X[E[0]], X[y]) == 0)
    print(f"c={c} d={d}: |E|={len(E)} hexagon lines inside={len(spread)} points covered={len(cover)} "
          f"max cover={max(cover.values())} spread={'YES' if ok else 'no'} orthogonality degree of first point={deg}")
