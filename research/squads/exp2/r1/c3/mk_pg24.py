# Build the incidence graph of PG(2,4) as a hub graph file ("K m" then "j k" lines).
# GF(4) = {0,1,a,a+1} encoded as 2-bit ints: 0, 1, 2 (= a), 3 (= a+1), with a^2 = a+1.
import itertools, sys

ADD = lambda x, y: x ^ y
MUL_T = [[0,0,0,0],[0,1,2,3],[0,2,3,1],[0,3,1,2]]
def mul(x, y): return MUL_T[x][y]

def normalised_triples():
    out = []
    for v in itertools.product(range(4), repeat=3):
        if v == (0, 0, 0):
            continue
        lead = next(c for c in v if c != 0)
        if lead == 1:          # first nonzero coordinate equal to 1
            out.append(v)
    return out

pts = normalised_triples()
lns = normalised_triples()     # dual coordinates
assert len(pts) == 21 and len(lns) == 21, (len(pts), len(lns))

def incident(P, L):
    s = 0
    for a, b in zip(P, L):
        s = ADD(s, mul(a, b))
    return s == 0

edges = []
for j, L in enumerate(lns):
    for k, P in enumerate(pts):
        if incident(P, L):
            edges.append((j, k))

# projective plane checks: every point on 5 lines, every line has 5 points, any two points share exactly one line
deg_l = [sum(1 for (j, k) in edges if j == t) for t in range(21)]
deg_p = [sum(1 for (j, k) in edges if k == t) for t in range(21)]
assert all(d == 5 for d in deg_l) and all(d == 5 for d in deg_p), (deg_l, deg_p)
on_line = {j: set(k for (jj, k) in edges if jj == j) for j in range(21)}
for a, b in itertools.combinations(range(21), 2):
    common = sum(1 for j in range(21) if a in on_line[j] and b in on_line[j])
    assert common == 1, (a, b, common)
print("PG(2,4) incidence graph ok: 21 points, 21 lines, 5 per line, 5 per point, 105 incidences")

out = sys.argv[1]
with open(out, "w") as f:
    f.write("21 %d\n" % len(edges))
    for j, k in edges:
        f.write("%d %d\n" % (j, k))
print("wrote", out, "edges", len(edges))
