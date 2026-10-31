# H(5): points = singular points; W_x = kernel of x-cross (totally singular plane, 31 pts).
# hexagon lines = lines L of Q with L inside W_z for every z in L.  Writes hexdata.pkl (points, lines).
exec(open('hexgraph.py').read().split('allpts = []')[0])
import pickle, time
t0 = time.time()
allpts = []; seen = set()
for v in itertools.product(range(p), repeat=N):
    if not any(v): continue
    nv = norm(v)
    if nv in seen: continue
    seen.add(nv)
    if Bq(nv, nv) == 0: allpts.append(nv)
P = len(allpts); idx = {v: i for i, v in enumerate(allpts)}
print("points", P, time.time()-t0, flush=True)
def Lmat(x):
    cols = [cross(x, [int(i == j) for i in range(N)]) for j in range(N)]
    return [[cols[j][i] for j in range(N)] for i in range(N)]
W = []
for x in allpts:
    ns = nullspace(Lmat(x), N); dim = len(ns)
    s = set()
    for cs in itertools.product(range(p), repeat=dim):
        if not any(cs): continue
        v = [sum(cs[k]*ns[k][i] for k in range(dim)) % p for i in range(N)]
        s.add(idx[norm(v)])
    W.append(s)
print("planes built", time.time()-t0, "sizes", set(len(w) for w in W), flush=True)
lines = set()
for i in range(P):
    for j in W[i]:
        if j == i: continue
        x, y = allpts[i], allpts[j]
        pts = set()
        for a, b in [(1, 0)] + [(t, 1) for t in range(p)]:
            pts.add(idx[norm([(a*x[k] + b*y[k]) % p for k in range(N)])])
        if all(pts <= W[z] for z in pts):
            lines.add(tuple(sorted(pts)))
lines = sorted(lines)
deg = [0]*P
for l in lines:
    for z in l: deg[z] += 1
print("hexagon lines", len(lines), "pts/line", set(len(l) for l in lines), "lines per point", set(deg), time.time()-t0, flush=True)
pickle.dump((allpts, lines), open("hexdata.pkl", "wb"))
