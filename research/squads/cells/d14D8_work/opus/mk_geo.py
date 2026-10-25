"""Level family with a geometric doubled matching: phi(p) = a line at hexagon distance dist (1, 3 or 5) from p.
python3 mk_geo.py q L k seed s1,s2 dist out   (hex sub-voltages random in Z_k, jump subs random; k=1: levels only)"""
import sys, subprocess, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d14D8_work')
from hexlib import load, write_base, hex_edges
q, L, k, seed = map(int, sys.argv[1:5]); shifts = [int(x) for x in sys.argv[5].split(',')]; dist = int(sys.argv[6]); out = sys.argv[7]
m = L * k
T = np.zeros((L, k), dtype=np.int64)
for x in range(m): T[x % L, x % k] = x
N, LP, PL, coord = load(q)
rng = np.random.default_rng(seed)
C = 24
cand = np.zeros((N, C), dtype=np.int64)
for p in range(N):
    l1 = PL[p]
    if dist == 1: pool = l1
    else:
        p2 = np.unique(LP[l1].ravel()); p2 = p2[p2 != p]
        l3 = np.setdiff1d(np.unique(PL[p2].ravel()), l1)
        if dist == 3: pool = l3
        else:
            pool = None
    if pool is None:
        pool = rng.integers(0, N, 4 * C)  # distance 5 is ~all lines
    cand[p] = rng.choice(pool, C, replace=len(pool) < C)
inp = f"{N} {C}\n" + "\n".join(" ".join(map(str, r)) for r in cand.tolist()) + "\n"
res = subprocess.run(['/home/user/degree-diameter/research/squads/cells/d14D8_work/pmatch', str(seed)], input=inp.encode(), capture_output=True)
phi = np.array(res.stdout.split(), dtype=np.int64)
assert (phi >= 0).all() and len(np.unique(phi)) == N, res.stderr
hv = rng.integers(0, k, LP.shape) if k > 1 else np.zeros(LP.shape, dtype=np.int64)
E = [hex_edges(LP, T[0, hv])]
for s in shifts:
    c = rng.integers(0, k, N)
    E.append(np.stack([np.arange(N), phi, T[s % L, c]], axis=1))
write_base(out, N, m, np.concatenate(E))
