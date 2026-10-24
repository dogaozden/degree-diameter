"""Covering labels + hop matching chosen geometrically: s(p) at point-line distance 3 or 5 (distance-1 excluded)."""
import random, sys, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/r1-d8/c6')
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d8')
from c6lib import load, collinear_lists, write_base, liftdiam
from models import perfect_matching
q = int(sys.argv[1]); M = int(sys.argv[2]); lab_file = sys.argv[3]; modes = [int(x) for x in sys.argv[4].split(',')]
H = load(q); N = H.N; X = collinear_lists(H)
t = [int(x) for x in open(lab_file).read().split()]
assert len(t) == N
for mode in modes:
    nbrs = []
    for p in range(N):
        S = set()
        for x in X[p]:
            for L in H.through[x]:
                S.add(int(L))
        if mode == 3:
            cand = sorted(S - set(int(L) for L in H.through[p]))
        else:
            cand = sorted(set(range(N)) - S)
        nbrs.append(cand)
    rng = random.Random(3)
    s = perfect_matching(N, nbrs, rng)
    path = f'/home/user/degree-diameter/research/squads/r1-d8/c6/geo_q{q}_M{M}_d{mode}.txt'
    write_base(path, H, M, t, s)
    t0 = time.time()
    unr, ecc, out = liftdiam(path, 8, 1)
    print(f'q={q} M={M} labels={lab_file.split("/")[-1]} hop distance {mode}: unreached={unr} max_ecc={ecc} secs={time.time()-t0:.1f}', flush=True)
