# Card r3c1: decision version of the orbit-union problem: is there a union of relaxed orbits of a subgroup K (of H1)
# with at least TARGET points?  Usage: dec.py ELEMENT_IDX_LIST(comma) TARGET SECONDS
import sys, json, time, threading
gens_idx = [int(x) for x in sys.argv[1].split(',')]
TARGET = int(sys.argv[2]); SECS = float(sys.argv[3])
args_save = sys.argv[:]
sys.argv = ['x', '/home/user/degree-diameter/research/squads/gqd5-r3/c1/H1.npy']
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r3/c1')
import numpy as np
import orbsat2 as O
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver
H = O.H; n = O.n; itertools = __import__('itertools')
gens = [H[i] for i in gens_idx]
orbs = O.orbits_of(gens)
good = [o for o in orbs if O.relaxed(o)]
m = len(good)
orb_of = [-1] * n
for i, o in enumerate(good):
    for p in o: orb_of[p] = i
clauses = set()
for k in range(len(O.S)):
    mem = O.G.lines[O.S[k]]
    for a, b in itertools.combinations(mem, 2):
        ia, ib = orb_of[a], orb_of[b]
        if ia >= 0 and ib >= 0: clauses.add(frozenset((ia, ib)))
for p in range(n):
    ip = orb_of[p]
    if ip < 0: continue
    nb = sorted(set(orb_of[r] for r in O.nbr[p] if orb_of[r] >= 0))
    # multiset of neighbour orbits: pairs of distinct neighbours in same orbit also matter
    cnt = {}
    for r in O.nbr[p]:
        x = orb_of[r]
        if x >= 0: cnt[x] = cnt.get(x, 0) + 1
    items = []
    for x, c in cnt.items(): items += [x] * min(c, 2)
    for x, y in itertools.combinations(sorted(items), 2):
        clauses.add(frozenset((ip, x, y)))
cls = [[-(v + 1) for v in c] for c in clauses]
# at-least-TARGET on the replicated literals
lits = []
for i, o in enumerate(good): lits += [i + 1] * len(o)
# weighted: replicate each orbit literal |O| times through a totalizer over the multiset
lit_multi = []
for i, o in enumerate(good): lit_multi += [i + 1] * len(o)
enc = CardEnc.atleast(lits=lit_multi, bound=TARGET, top_id=m, encoding=EncType.seqcounter)
allc = cls + enc.clauses
print('K-order-gens', len(gens), 'orbits', len(orbs), 'relaxed', m, 'clauses', len(allc), flush=True)
if m == 0 or sum(len(o) for o in good) < TARGET:
    print('RESULT none-possible'); sys.exit(0)
s = Solver(name='g4', bootstrap_with=allc)
timer = threading.Timer(SECS, lambda: s.interrupt()); timer.start()
t0 = time.time()
res = s.solve_limited(expect_interrupt=True)
timer.cancel()
if res:
    model = s.get_model()
    sel = [i for i in range(m) if model[i] > 0]
    T = sorted(p for i in sel for p in good[i])
    ok = O.relaxed(T)
    print('RESULT SAT size', len(T), 'relaxed-check', ok, 'time %.1f' % (time.time() - t0), flush=True)
    if ok:
        json.dump(T, open('/home/user/degree-diameter/research/squads/gqd5-r3/c1/dec_%d.json' % TARGET, 'w'))
elif res is False:
    print('RESULT UNSAT time %.1f' % (time.time() - t0), flush=True)
else:
    print('RESULT TIMEOUT time %.1f' % (time.time() - t0), flush=True)
