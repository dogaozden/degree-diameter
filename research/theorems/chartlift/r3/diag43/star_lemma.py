"""Local lemma behind the (4,3) diagonal question.  In the star of a chart apex (a PG(2,3)) the A-side diagonal uses
the 3 edge directions E (towards the other apexes) and the 3 U-line directions U; the map A_s swaps the roles on side B
(U becomes the b-edge directions, E becomes the V-line directions).  For every triangle E and every 3-set U of points
outside E, count f = #{u in U off all sides of E} (free U-lines) and f' = #{e in E off every line through two points of
U} (free V-lines).  Prints the distribution of (f, f') and the maximum of f + f'."""
import itertools
q = 3
pts = []
for v in itertools.product(range(q), repeat=3):
    if any(v):
        f = next(x for x in v if x); inv = 1 if f == 1 else 2
        w = tuple((x * inv) % q for x in v)
        if w not in pts: pts.append(w)
assert len(pts) == 13
def col(a, b, c):
    M = [a, b, c]
    d = (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
         + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0])) % q
    return d == 0
E = [(1, 0, 0), (0, 1, 0), (0, 0, 1)]
rest = [p for p in pts if p not in E]
dist = {}
for U in itertools.combinations(rest, 3):
    f = sum(1 for u in U if not any(col(u, E[i], E[j]) for i, j in [(0, 1), (0, 2), (1, 2)]))
    fp = sum(1 for e in E if not any(col(e, U[i], U[j]) for i, j in [(0, 1), (0, 2), (1, 2)]))
    key = (f, fp, 'U collinear' if col(*U) else 'U triangle')
    dist[key] = dist.get(key, 0) + 1
for k in sorted(dist): print(k, dist[k])
print('max f + f\' =', max(a + b for a, b, _ in dist))
