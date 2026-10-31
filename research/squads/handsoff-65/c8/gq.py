# W(5) = GQ(5,5): points PG(3,5), lines = totally isotropic lines of x0y1-x1y0+x2y3-x3y2. Incidence graph -> gq.edges
import itertools
q = 5
def form(x, y): return (x[0]*y[1] - x[1]*y[0] + x[2]*y[3] - x[3]*y[2]) % q
def norm(v):
    for x in v:
        if x % q:
            inv = pow(x, q-2, q); return tuple((y*inv) % q for y in v)
pts = sorted({norm(v) for v in itertools.product(range(q), repeat=4) if any(v)})
pidx = {v: i for i, v in enumerate(pts)}
lines = set()
for a in pts:
    for b in pts:
        if a < b and form(a, b) == 0:
            L = set()
            for s, t in [(1, 0)] + [(t, 1) for t in range(q)]:
                L.add(pidx[norm([(s*a[k] + t*b[k]) % q for k in range(4)])])
            lines.add(tuple(sorted(L)))
lines = sorted(lines)
print(len(pts), len(lines), set(len(l) for l in lines))
n = len(pts) + len(lines)
with open('gq.edges', 'w') as f:
    f.write(f"{n}\n")
    for k, l in enumerate(lines):
        for z in l:
            f.write(f"{z} {len(pts)+k}\n")
