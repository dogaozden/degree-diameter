import sys, time, random
sys.path.insert(0, '/home/user/degree-diameter/research/squads/b48/r3/d15')
from grp_mat import make_group
from coset import subgroups4, build_nbr, cost_of, write_edges
t0 = time.time()
N, mul = make_group('PGL', 23)
subs = subgroups4(N, mul)
H = (0, 1583, 10691, 11659)
K0 = (0, 5433, 6687, 8425)
sH = set(H)
cands = [s for s in subs if set(s) & sH == {0}]
random.Random(7).shuffle(cands)
best = (10**9, None)
n_eval = 0
for K in cands:
    if time.time() - t0 > 52: break
    nbr, idH, idK, NL = build_nbr(N, mul, H, K)
    c = cost_of(nbr, NL); n_eval += 1
    if c < best[0]:
        best = (c, K)
        print("best", c, "K", K, f"t={time.time()-t0:.1f}", flush=True)
        if c == 0:
            write_edges('/home/user/degree-diameter/research/squads/b48/r3/d15/pgl23_sweep_valid.edges', nbr, NL)
print("evals", n_eval, "of", len(cands), "best", best, "H", H, flush=True)
