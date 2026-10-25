"""Build the full q=3 graph: main graph with the 112 spread points freed + L-hubs (point-vertex slots) + P-hubs
(line-vertex slots). Usage: buildfam.py LFAM PFAM OUT.edges  (LFAM/PFAM: files from hubsa; empty name = none)."""
import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d12D7-r2/c8/src')
from q3lib import *
LP = load_hex(); M = load_phi(); S = load_spread()
F = sorted(set(p for l in S for p in LP[l]))
n0 = NL * B
E = main_edges(LP, M, set(F))
def read_fam(fn):
    if not fn or fn == '-': return []
    t = open(fn).read().split(); K = int(t[0]); v = [int(x) for x in t[1:1 + 5 * K]]
    return [v[5 * h:5 * h + 5] for h in range(K)]
Lf = read_fam(sys.argv[1]); Pf = read_fam(sys.argv[2])
nL = len(Lf); nP = len(Pf); n = n0 + nL + nP
for j, hub in enumerate(Lf):
    for i, s in enumerate(hub):
        assert s % 5 == i; fi = s // 5
        E.append((n0 + j, ID(F[fi], i)))
for k, hub in enumerate(Pf):
    for i, s in enumerate(hub):
        assert s % 5 == i; fi = s // 5
        E.append((n0 + nL + k, ID(N + M[F[fi]], i)))
write_edges(sys.argv[3], n, E)
print('n', n, 'L hubs', nL, 'P hubs', nP, 'edges', len(E))
