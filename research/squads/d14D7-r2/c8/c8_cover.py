"""c8: coverage of the base points by the 4-balls of freed points (quotient graph, no hubs).
A point-like super-hub w joined to the line-side hubs z_i of units i (freed point p_i) reaches (y,g) within 6 iff
some i has quotient distance d(p_i, y) <= 4 (w's copies are all free). Greedy set cover over the units' freed points.
Usage: python3 c8_cover.py GHFILE STATE UNITS BUDGET"""
import sys, collections
GH, STATE, UNITS, BUDGET = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
tok = open(GH).read().split()
P, q = int(tok[0]), int(tok[1]); Q1 = q + 1
lineP = [[int(x) for x in tok[2 + l * Q1: 2 + (l + 1) * Q1]] for l in range(P)]
pl = [[] for _ in range(P)]
for l in range(P):
    for p in lineP[l]: pl[p].append(l)
st = open(STATE).read().split()
J, m = int(st[2]), int(st[3])
idx = 7
sig = [[0] * P for _ in range(J)]; hv = [[0] * P for _ in range(J)]
for p in range(P):
    for t in range(J):
        sig[t][p] = int(st[idx]); hv[t][p] = int(st[idx + 1]); idx += 2
inv = [[0] * P for _ in range(J)]
for t in range(J):
    for p in range(P): inv[t][sig[t][p]] = p
units = []
for ln in open(UNITS):
    a = ln.split()
    if len(a) >= 2: units.append((int(a[0]), int(a[1]) - 1))
deleted = set((p, t) for p, t in units)
def nbrs_point(x):
    for l in pl[x]: yield P + l
    for t in range(J):
        if (x, t) not in deleted: yield P + sig[t][x]
def nbrs_line(l):
    for x in lineP[l]: yield x
    for t in range(J):
        x = inv[t][l]
        if (x, t) not in deleted: yield x
def ball(p, R):
    """points within quotient distance R of point p (base graph with deletions)"""
    seen = {p}; front = [p]; pts = {p}
    for d in range(1, R + 1):
        nf = []
        for x in front:
            if x < P:
                for y in nbrs_point(x):
                    if y not in seen: seen.add(y); nf.append(y)
            else:
                for y in nbrs_line(x - P):
                    if y not in seen: seen.add(y); nf.append(y)
        front = nf
    return set(v for v in seen if v < P)
balls = [ball(p, 4) for p, t in units]
N = P
print('units', len(units), 'points', N, 'ball4 sizes min/avg/max %d %.0f %d' % (min(map(len, balls)), sum(map(len, balls)) / len(balls), max(map(len, balls))))
covered = set(); chosen = []
for k in range(BUDGET):
    best = max(range(len(units)), key=lambda i: len(balls[i] - covered) if i not in chosen else -1)
    chosen.append(best); covered |= balls[best]
    print('greedy k=%d unit=%d (p=%d t=%d) gain=%d uncovered=%d' % (k + 1, best, units[best][0], units[best][1] + 1, len(balls[best] - covered) if False else 0, N - len(covered)))
print('chosen', chosen)
rnd = __import__('random').Random(1); sample = rnd.sample(range(len(units)), min(BUDGET, len(units)))
cov = set()
for i in sample: cov |= balls[i]
print('random %d units: uncovered %d' % (BUDGET, N - len(cov)))
