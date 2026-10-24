"""c8: coverage of the base points by a point-like super-hub w joined to line-side hubs z_i (set S).
w reaches (y,g) within 6 iff y is within quotient distance 5 of some z_i in S (quotient graph: base H(q) + matchings with
the unit deletions, hub z_i ~ p_i, hub z'_k ~ l_k, hub-graph links z_i ~ z'_k from the uhcheck EXTRAS-style file x).
Each z_i gives a ball C_i (points within 5 of z_i). Greedy set cover over the line-side hubs, budget BUDGET.
Usage: python3 c8_cover2.py GHFILE STATE UNITS HUBX BUDGET"""
import sys, random
GH, STATE, UNITS, HUBX, BUDGET = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4], int(sys.argv[5])
tok = open(GH).read().split()
P, q = int(tok[0]), int(tok[1]); Q1 = q + 1
lineP = [[int(x) for x in tok[2 + l * Q1: 2 + (l + 1) * Q1]] for l in range(P)]
pl = [[] for _ in range(P)]
for l in range(P):
    for p in lineP[l]: pl[p].append(l)
st = open(STATE).read().split()
J, m = int(st[2]), int(st[3])
idx = 7
sig = [[0] * P for _ in range(J)]
for p in range(P):
    for t in range(J):
        sig[t][p] = int(st[idx]); idx += 2
inv = [[0] * P for _ in range(J)]
for t in range(J):
    for p in range(P): inv[t][sig[t][p]] = p
units = []
for ln in open(UNITS):
    a = ln.split()
    if len(a) >= 2: units.append((int(a[0]), int(a[1]) - 1))
NU = len(units)
deleted = set(units)
# hub nodes: hub 2i (line-side, ~ p_i), 2i+1 (point-side, ~ l_i); line index of unit i
ul = []
for p, t in units: ul.append(sig[t][p])
assert len(set(units)) == len(units)
hx = open(HUBX).read().split()
NS = int(hx[0]); xe = [(int(hx[1 + 2 * k]), int(hx[2 + 2 * k])) for k in range((len(hx) - 1) // 2)]
hubadj = {}
for a, b in xe:
    hubadj.setdefault(a, []).append(b); hubadj.setdefault(b, []).append(a)
p2h = {}; l2h = {}
for i in range(NU):
    p2h.setdefault(units[i][0], []).append(2 * i); l2h.setdefault(ul[i], []).append(2 * i + 1)
def nb_point(x):
    for l in pl[x]: yield ('L', l)
    for t in range(J):
        if (x, t) not in deleted: yield ('L', sig[t][x])
    for h in p2h.get(x, []): yield ('H', h)
def nb_line(l):
    for x in lineP[l]: yield ('P', x)
    for t in range(J):
        x = inv[t][l]
        if (x, t) not in deleted: yield ('P', x)
    for h in l2h.get(l, []): yield ('H', h)
def nb_hub(h):
    i = h // 2
    if h % 2 == 0: yield ('P', units[i][0])
    else: yield ('L', ul[i])
    for b in hubadj.get(h, []): yield ('H', b)
def ball_from_hub(h0, R):
    seen = {('H', h0)}; front = [('H', h0)]; pts = set()
    for d in range(1, R + 1):
        nf = []
        for node in front:
            k, x = node
            it = nb_point(x) if k == 'P' else nb_line(x) if k == 'L' else nb_hub(x)
            for y in it:
                if y not in seen: seen.add(y); nf.append(y)
        front = nf
    for k, x in seen:
        if k == 'P': pts.add(x)
    return pts
balls = []
for i in range(NU):
    balls.append(ball_from_hub(2 * i, 5))
print('units NU=%d hub-graph links=%d points=%d; ball5(z_i) sizes min/avg/max %d %.0f %d' % (
    NU, len(xe), P, min(map(len, balls)), sum(map(len, balls)) / NU, max(map(len, balls))), flush=True)
covered = set(); chosen = []
for k in range(BUDGET):
    best = max((i for i in range(NU) if i not in chosen), key=lambda i: len(balls[i] - covered))
    chosen.append(best); covered |= balls[best]
    print('greedy step %d: hub z_%d gain %d, uncovered %d' % (k + 1, best, len(balls[best] - covered) if False else 0, P - len(covered)), flush=True)
print('greedy uncovered after %d hubs: %d of %d points' % (BUDGET, P - len(covered), P))
rnd = random.Random(1); samp = rnd.sample(range(NU), min(BUDGET, NU)); cov = set()
for i in samp: cov |= balls[i]
print('random %d hubs: uncovered %d' % (BUDGET, P - len(cov)))
