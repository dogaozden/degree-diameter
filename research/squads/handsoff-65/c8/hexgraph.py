# Split Cayley hexagon H(5) from G2(5) on V=F5^7: points = singular points of B, lines = spans of collinear
# pairs (x x y = 0). Incidence graph: vertices 0..3905 points, 3906..7811 lines.
from g2lie import *
import pickle
_pos = {}; _c = 0
for _i in range(N):
    for _j in range(_i, N):
        _pos[(_i, _j)] = _c; _c += 1
B = [[Bbasis[0][_pos[(min(i, j), max(i, j))]] for j in range(N)] for i in range(N)]
Binv = minv(B)
def phv(x, y):
    # phi(x,y,e_j) for each j, as a row vector
    return [sum(x[a]*y[b]*ph(a, b, j) for a in range(N) for b in range(N) if x[a] and y[b]) % p for j in range(N)]
def cross(x, y):
    w = phv(x, y)
    return [sum(Binv[i][j]*w[j] for j in range(N)) % p for i in range(N)]
def Bq(x, y): return sum(x[i]*B[i][j]*y[j] for i in range(N) for j in range(N)) % p
def norm(v):
    for x in v:
        if x % p:
            inv = pow(x, p-2, p)
            return tuple((y*inv) % p for y in v)
    return None
allpts = []
seen = set()
for v in itertools.product(range(p), repeat=N):
    if not any(v): continue
    nv = norm(v)
    if nv in seen: continue
    seen.add(nv)
    if Bq(nv, nv) == 0: allpts.append(nv)
print("singular points:", len(allpts))
idx = {v: i for i, v in enumerate(allpts)}
P = len(allpts)
# collinearity
coll = [[] for _ in range(P)]
for i, x in enumerate(allpts):
    for j in range(i+1, P):
        y = allpts[j]
        if not any(cross(x, y)) and Bq(x, y) == 0:
            coll[i].append(j); coll[j].append(i)
print("collinear counts sample:", sorted(set(len(c) for c in coll)))
lines = set()
for i in range(P):
    for j in coll[i]:
        if j <= i: continue
        x, y = allpts[i], allpts[j]
        pts = set()
        for a, b in [(1,0)] + [(t,1) for t in range(p)]:
            v = norm([(a*x[k] + b*y[k]) % p for k in range(N)])
            pts.add(idx[v])
        lines.add(tuple(sorted(pts)))
lines = sorted(lines)
print("lines:", len(lines), "pts per line:", set(len(l) for l in lines))
pickle.dump((allpts, lines), open("hexdata.pkl", "wb"))
