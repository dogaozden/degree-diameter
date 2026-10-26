import sys, pickle
sys.path.insert(0, "/home/user/degree-diameter/research/squads/own-small/r1/a1/work")
from common import *
N, M = load_group()
inv = inverses(N, M)
rng = np.random.default_rng(1)
for _ in range(20000):
    a, b, c = rng.integers(0, N, 3)
    assert M[M[a, b], c] == M[a, M[b, c]]
subs = {}
for g in range(N):
    H = closure(M, [g]); subs.setdefault(H, [g])
cyc = list(subs)
for A in cyc:
    for g in range(N):
        if g in A: continue
        H = closure(M, [g] + list(subs[A]))
        subs.setdefault(H, [g] + list(subs[A]))
# close again with pairs of found subgroups' gens
for A in list(subs):
    for B in list(subs):
        pass
from collections import Counter
print("total subgroups found", len(subs), Counter(len(H) for H in subs).most_common())
pickle.dump({tuple(sorted(H)): gens for H, gens in subs.items()}, open("/home/user/degree-diameter/research/squads/own-small/r1/a1/work/subs.pkl", "wb"))
