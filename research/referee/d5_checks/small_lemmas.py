"""Lemma 1.2(c) (exhaustive triad centre counts), Lemma 1.3 (q = 3..13), Lemma 1.4 (q = 2, 4, 8),
and the A-hub structure of the (13,5) solution file."""
import itertools, random, sys, json
from collections import Counter
from gf import GF
from gq import W, Q4
from families import lemma13_partial_ovoid, lemma14_duality, lemma11_spread

for q in (3, 5):
    F = GF(q)
    for G, name in ((W(F), 'W'), (Q4(F), 'Q(4,q)')):
        c = Counter()
        for x, y, z in itertools.combinations(range(G.N), 3):
            if y in G.collinear[x] or z in G.collinear[x] or z in G.collinear[y]:
                continue
            c[len(G.collinear[x] & G.collinear[y] & G.collinear[z])] += 1
        print("q=%d %s: point triads by number of centres (all triads): %s" % (q, name, dict(sorted(c.items()))))
rng = random.Random(5)
for q in (3, 5, 7, 9, 11, 13):
    F = GF(q); Wq = W(F)
    if q == 3:      # the q = 3 version: three orbits plus (x,0), x = (1,-1): 7 points
        m = F.mul; perp = lambda v: (F.neg[v[1]], v[0])
        a = [(1, 0), (0, 1), (1, 1)]; b = [perp(a[(i - 1) % 3]) for i in range(3)]
        from gf import normalize
        pts = [(a[i][0], a[i][1], m[c][b[i][0]], m[c][b[i][1]]) for i in range(3) for c in range(1, q)] + [(1, F.neg[1], 0, 0)]
        S = [Wq.idx[normalize(F, p)] for p in pts]
        ok = all(y not in Wq.collinear[x] for x, y in itertools.combinations(S, 2))
        print("Lemma 1.3, q=3 variant: %d points, partial ovoid: %s" % (len(set(S)), ok))
    else:
        for t in range(3):
            S = lemma13_partial_ovoid(F, Wq, rng)       # asserts 3q-1 distinct pairwise non-collinear points
        print("Lemma 1.3, q=%d: 3q-1 = %d points, partial ovoid of W(q) (3 random choices of tau, z)" % (q, 3 * q - 1))
for q in (2, 4, 8):
    F = GF(q); Wq = W(F)
    psi, phi = lemma14_duality(F, Wq)                    # asserts bijection and incidence preservation
    OW = [psi[l] for l in lemma11_spread(F, Wq)]
    print("Lemma 1.4, q=%d: (phi, psi) is a duality of W(q); psi(spread) is an ovoid: %s" %
          (q, all(y not in Wq.collinear[x] for x, y in itertools.combinations(OW, 2)) and len(OW) == q * q + 1))
if len(sys.argv) > 1:
    sol = json.load(open(sys.argv[1]))
    types = sol['types']; Ts = set(sol['T'])
    Wl = [set(l) for l in sol['W_lines']]
    serv = {}
    for g, slots in enumerate(sol['Ahub_slots']):
        for (j, e, arc) in slots:
            if types[arc[0]] == 'D' and types[arc[1]] == 'H' and e in Ts:
                serv.setdefault(e, set()).add(g)
    part = [l for l in Ts if any(l in w and len(w & Ts) == 2 for w in Wl)]
    print("record: partnered lines %d; A-hubs serving each partnered line on the five D->H arcs: %s" %
          (len(part), Counter(len(serv[l]) for l in part)))
