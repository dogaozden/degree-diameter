# Bi-coset scan on G = (PSL|PGL)(2,q) x Z_c with random order-4 subgroup pairs (H cap K = 1).
import sys, time, random
sys.path.insert(0, '/home/user/degree-diameter/research/squads/b48/r3/d15')
import numpy as np
from grp_mat import make_group
from coset import subgroups4, build_nbr, cost_of, write_edges
specs = sys.argv[1].split(',')   # e.g. PSL:11:16,PGL:7:30
samples = int(sys.argv[2]); tlimit = float(sys.argv[3]); seed = int(sys.argv[4]); tag = sys.argv[5]
t0 = time.time()
def make_prod(kind, q, c):
    G, mulG = make_group(kind, q)
    def mul(x, y):
        x = np.asarray(x, dtype=np.int64); y = np.asarray(y, dtype=np.int64)
        x, y = np.broadcast_arrays(x, y)
        g1, z1 = x // c, x % c
        g2, z2 = y // c, y % c
        return mulG(g1, g2) * c + (z1 + z2) % c
    return G * c, mul
rng = random.Random(seed)
overall = None
for sp in specs:
    kind, q, c = sp.split(':'); q = int(q); c = int(c)
    N, mul = make_prod(kind, q, c)
    if time.time() - t0 > tlimit: break
    subs = subgroups4(N, mul)
    sets = [set(s) for s in subs]
    best = None; res = []; done = 0; tries = 0
    while done < samples and time.time() - t0 < tlimit:
        tries += 1
        if tries > 40 * samples: break
        a = rng.randrange(len(subs)); b = rng.randrange(len(subs))
        if a == b or (sets[a] & sets[b]) != {0}: continue
        nbr, idH, idK, NL = build_nbr(N, mul, subs[a], subs[b])
        cst = cost_of(nbr, NL)
        done += 1
        res.append(cst)
        if best is None or cst < best[0]:
            best = (cst, subs[a], subs[b])
            if overall is None or cst < overall[0]:
                overall = (cst, sp, subs[a], subs[b])
                if cst == 0:
                    write_edges(f"/home/user/degree-diameter/research/squads/b48/r3/d15/{tag}_valid.edges", nbr, NL)
    print(f"{sp}: order {N} n={N//2} subgroups4={len(subs)} evals={done} best={best[0] if best else None} "
          f"median={sorted(res)[len(res)//2] if res else None} H={best[1] if best else None} K={best[2] if best else None} t={time.time()-t0:.1f}", flush=True)
print("OVERALL", overall, flush=True)
