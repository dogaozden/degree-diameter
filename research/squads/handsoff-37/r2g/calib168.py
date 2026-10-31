# r2g calibration: colour-preserving automorphisms of conder168 (H, order 252) as a permutation group; the
# orbit-level engine (Comp / LNS) should recover a far-0 completion for the composition [stab order 3 orbit] | [same].
import sys, os, time, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import orb
from orb import *
from lns import Comp, lns
from collections import deque
SQ = '/home/user/degree-diameter/research/squads/handsoff-37/'
toks = open(SQ + 'shared/seeds/conder168.edges').read().split()
n = int(toks[0]); N = [[] for _ in range(n)]
for i in range(1, len(toks), 2):
    a, b = int(toks[i]), int(toks[i+1]); N[a].append(b); N[b].append(a)
col = [-1]*n; col[0] = 0; dq = deque([0])
while dq:
    x = dq.popleft()
    for y in N[x]:
        if col[y] < 0: col[y] = 1 - col[x]; dq.append(y)
lines = open(SQ + 'c5/out/aut168.txt').read().split('\n')
auts = [tuple(int(x) for x in l.split()) for l in lines[1:] if l.strip()]
print('auts', len(auts), file=sys.stderr)
H = [p for p in auts if all(col[p[v]] == col[v] for v in range(n))]
print('colour-preserving', len(H), file=sys.stderr)
G = group_from_gens(H)   # uses all elements as generators (slow but exact)
print('group order', G['N'], flush=True)
# stabiliser of vertex 0 inside H
ident_index = 0
stab = frozenset(i for i, p in enumerate(G['elems']) if p[0] == 0)
orbA = sorted(set(p[0] for p in G['elems'])); print('orbit of 0 size', len(orbA), flush=True)
b0 = [v for v in range(n) if col[v] == 1][0]
orbB = sorted(set(p[b0] for p in G['elems'])); print('orbit of B vertex size', len(orbB), flush=True)
stabB = frozenset(i for i, p in enumerate(G["elems"]) if p[b0] == b0)
S = Setup(G, [stab, stabB])
print('orbit sizes', S.sizes, flush=True)
comp = Comp(S, [0], [1])
print('m', comp.m, 'edge orbits', comp.E, 'feasible', comp.feasible, flush=True)
rng = random.Random(1); orb.RNG = rng
t0 = time.time(); seen = {}
for trial in range(200):
    ch = comp.complete([], rng)
    if ch is None: continue
    nn, adj, ev = comp.graph(ch)
    f = far_count(nn, adj)
    seen[f] = seen.get(f, 0) + 1
    if time.time() - t0 > 120: break
print('random completions far histogram', sorted(seen.items())[:15], 'time', round(time.time()-t0,1), flush=True)
