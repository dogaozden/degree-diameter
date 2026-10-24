"""Per-apex tuples for the tetrahedron-tetrahedron case of the (4,3) diagonal question.
Star of apex s = PG(2,3).  E = 3 edge directions (a triangle: the w's span PG(3,3)); U = the 3 directions of the U-lines
(a triangle when the b's span PG(3,3), since A_s maps U onto the b-edge directions at b_s).
Side A at s: a U-line is free (off every face through w_s: star point off all sides of E) -> covers 2 interior points
and 1 face-free point of the opposite face; a face line (on a side of E, not a vertex) -> covers 2 face-free points of
one face through w_s (and 1 edge point); a vertex of E = an edge (covers nothing new).
Side B at s: the same with the roles of E and U swapped (V-lines = images of E, b-edges = images of U).
Prints every achievable (f, g, f', g') and the best totals."""
import itertools
q = 3
pts = []
for v in itertools.product(range(q), repeat=3):
    if any(v):
        f0 = next(x for x in v if x); inv = 1 if f0 == 1 else 2
        w = tuple((x * inv) % q for x in v)
        if w not in pts: pts.append(w)
def col(a, b, c):
    M = [a, b, c]
    return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
            + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0])) % q == 0
def classify(X, Y):
    """for each point of Y: 'vertex' if in X, 'side' if on a line through two points of X, else 'free'."""
    out = []
    for y in Y:
        if y in X: out.append('vertex')
        elif any(col(y, X[i], X[j]) for i, j in [(0, 1), (0, 2), (1, 2)]): out.append('side')
        else: out.append('free')
    return out
E = [(1, 0, 0), (0, 1, 0), (0, 0, 1)]
tuples = {}
for U in itertools.combinations(pts, 3):
    if col(*U): continue                      # b's span PG(3,3): U is a triangle
    cu = classify(E, U); ce = classify(list(U), E)
    t = (cu.count('free'), cu.count('side'), ce.count('free'), ce.count('side'))
    tuples[t] = tuples.get(t, 0) + 1
print('achievable (f, g, f\', g\') per apex [count of U]:')
for t in sorted(tuples): print('  ', t, tuples[t])
best = None
T = list(tuples)
ok = []
for combo in itertools.combinations_with_replacement(T, 4):
    f = sum(c[0] for c in combo); g = sum(c[1] for c in combo); fp = sum(c[2] for c in combo); gp = sum(c[3] for c in combo)
    if f >= 4 and fp >= 4 and f + 2 * g >= 16 and fp + 2 * gp >= 16: ok.append(combo)
print('4-apex combinations meeting f>=4, f\'>=4, f+2g>=16, f\'+2g\'>=16:', len(ok))
for c in ok[:20]: print('  ', c)
