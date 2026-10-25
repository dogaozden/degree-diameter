# sample random isometries of V, record permutations of E realising elements of projective order d | 1332
import sys, time, math, json
import numpy as np
from orth import *
secs = float(sys.argv[1]); seed = int(sys.argv[2])
rng = np.random.default_rng(seed)
T = 1332
divs = [d for d in range(2, T + 1) if T % d == 0]
found = {}
hist = {}
t0 = time.time(); samples = 0
while time.time() - t0 < secs:
    k = int(rng.integers(3, 13))
    g = rand_elem(rng, k)
    perm = perm_of(g)
    cyc = cycles(perm)
    n = 1
    for c in cyc: n = lcm(n, len(c))
    samples += 1
    hist[n] = hist.get(n, 0) + 1
    for d in divs:
        if n % d == 0 and d not in found:
            found[d] = pperm(perm, n // d)
            print("order", d, "found from projective order", n, "after", samples, "samples", flush=True)
    if len(found) == len(divs) and 1332 in found: break
np.savez_compressed(f"elems_seed{seed}.npz", **{f"d{d}": found[d] for d in found})
print("samples", samples, "found orders", sorted(found), flush=True)
top = sorted(hist.items(), key=lambda kv: -kv[1])[:15]
print("projective orders seen (order:count, top15):", top)
