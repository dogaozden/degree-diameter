# Sample isometries of V = {x4 = -x0} (E = Q^-(5,11)) whose projective order is divisible by 11 (non-trivial unipotent
# part) and save powers of order d (11 | d) with distinct orbit-size profiles as permutation files for orbitclique.
# Usage: python3 sample11.py SECONDS SEED OUTDIR
import sys, time, os
from collections import Counter
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d14D7-r3/c3')
from orth import *
secs = float(sys.argv[1]); seed = int(sys.argv[2]); outd = sys.argv[3]
os.makedirs(outd, exist_ok=True)
rng = np.random.default_rng(seed)
store = {}
t0 = time.time(); samples = 0
while time.time() - t0 < secs:
    k = int(rng.integers(2, 13))
    g = rand_elem(rng, k)
    perm = perm_of(g)
    cyc = cycles(perm)
    n = 1
    for c in cyc: n = lcm(n, len(c))
    samples += 1
    if n % 11: continue
    for d in range(11, n + 1, 11):
        if n % d: continue
        h = pperm(perm, n // d)
        fp = tuple(sorted(Counter(len(c) for c in cycles(h)).items()))
        key = (d, fp)
        if key in store: continue
        store[key] = h
        name = f"o{d}_{len([1 for kk in store if kk[0] == d])}_s{seed}"
        np.savetxt(f"{outd}/{name}.txt", h, fmt='%d')
        print(name, "profile", fp, flush=True)
print("samples", samples, "kept", len(store), flush=True)
