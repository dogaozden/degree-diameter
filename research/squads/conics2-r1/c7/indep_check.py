# Independent check of the definition: for each L in G, the other G-lines meeting L all pass through one point of L.
import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/conics2-r1/c7')
from common import *
q = int(sys.argv[1]); fn = sys.argv[2]
q, N, LP, PL, X = load(f'{D}/data/hex_q{q}.bin')
G = [int(t) for t in open(fn).read().split()]
assert len(set(G)) == len(G)
pts = {L: set(LP[L].tolist()) for L in range(N)}
ok = True
for L in G:
    meet = set()
    for M in G:
        if M == L: continue
        common = pts[L] & pts[M]
        if common:
            assert len(common) == 1
            meet |= common
    if len(meet) > 1:
        ok = False; break
print('q', q, 'size', len(G), 'independent check valid', ok)
