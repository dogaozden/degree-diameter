import sys, time, random, numpy as np
sys.path.insert(0,'/home/user/degree-diameter/research/squads/hexfam_r1/c8')
from chart import *
q = int(sys.argv[1]); seed = int(sys.argv[2]); trials = int(sys.argv[3])
ch = Chart(q); rng = random.Random(seed); nrng = np.random.default_rng(seed)
res = []
t0 = time.time()
for tr in range(trials):
    M = ch.random_orthogonal(rng, nref=rng.randint(3, 7))
    o = matpow_order(M, q)
    if o is None or o < 2 or o > 60: continue
    # optional scalar multiple (similitude)
    lam = rng.choice([1]*3 + list(range(2, q)))
    M2 = (lam * M) % q
    t = np.zeros(5, dtype=np.int64)
    label, size, ov = cyc_orbits(ch, M2, t)
    vids, A = orbit_graph(ch, label, size, ov)
    w = size[np.nonzero(ov)[0]].astype(np.int64)
    if len(vids) == 0: continue
    tot, cl = greedy_clique(w, A, nrng, restarts=20)
    dens = A.sum() / max(1, len(vids) * (len(vids) - 1))
    print(f"order={o} lam={lam} valid_orbits={len(vids)} sizes={sorted(set(size[np.nonzero(ov)[0]].tolist()))} density={dens:.3f} greedy_total={tot} t={time.time()-t0:.0f}s", flush=True)
    res.append((tot, o, lam, M2.tolist()))
res.sort(reverse=True)
print("TOP", res[:5])
