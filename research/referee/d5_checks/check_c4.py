"""Computer-checked 6.5: the 3-point freed set of squad card c4 on a non-friendly H->H transition of Q(4,5).
Only the labelling of Q(4,5) is taken from the writer's gqlib (validated here against the GQ axioms);
conditions (E2), (E3), the two-level BFS and the triad counts are my own code."""
import sys, json, itertools
from gq import GQ
from test_theorems import two_level_bad, E2E3
lines = json.load(open(sys.argv[1]))      # Q(4,5) lines as point lists, dumped from the writer's gqlib.Q4(5)
G = GQ(lines, len(lines))
G.check_axioms(5, 5)
d = json.load(open(sys.argv[2]))
M, R = d['M'], d['R']
assert sorted(M) == list(range(G.N))
print("R =", R, "pairwise non-collinear:", all(b not in G.collinear[a] for a, b in itertools.combinations(R, 2)))
e2, e3 = E2E3(G, 'H', 'H', M, R)
bad = two_level_bad(G, 'H', 'H', M, R)
print("(E2) %s (E3) %s; two-level pairs beyond distance 5: %d" % (e2, e3, len(bad)))
cen = set.intersection(*[G.collinear[x] for x in R])
img = [M[x] for x in R]
print("images pairwise non-concurrent:", all(b not in G.meets[a] for a, b in itertools.combinations(img, 2)))
cen2 = set.intersection(*[G.meets[l] for l in img])
print("triad centres: points %d, image lines %d" % (len(cen), len(cen2)))
print("(H3) holds at:", [x for x in R if {M[a] for a in G.collinear[x]} == G.meets[M[x]]])
