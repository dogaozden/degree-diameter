# check_orth.py FLAGS: pairwise non-orthogonality of the points of a flag file, using the E11.map coordinates and
# the form B(x,y) = x0y4 + x4y0 + x1y5 + x5y1 + x2y6 + x6y2 - 2x3y3 (mod 11); prints the number of orthogonal pairs.
import sys
MAP = "/home/user/degree-diameter/research/cell147/data/E11.map"
q = 11
pts = {}
with open(MAP) as f:
    for line in f:
        t = list(map(int, line.split()))
        pts[t[0]] = (t[1], t[2:9])          # point id -> (spread line id, coords x0..x6)
flags = [tuple(map(int, l.split())) for l in open(sys.argv[1]) if l.strip()]
pids = [p for p, _ in flags]
assert len(set(pids)) == len(pids), "repeated point"
for p, l in flags:
    assert pts[p][0] == l, "line is not the spread line of the point"
def B(x, y):
    return (x[0]*y[4] + x[4]*y[0] + x[1]*y[5] + x[5]*y[1] + x[2]*y[6] + x[6]*y[2] - 2*x[3]*y[3]) % q
X = [pts[p][1] for p in pids]
bad = sum(1 for i in range(len(X)) for j in range(i+1, len(X)) if B(X[i], X[j]) == 0)
print(f"{len(flags)} flags, distinct points, spread lines match, orthogonal pairs = {bad}")
