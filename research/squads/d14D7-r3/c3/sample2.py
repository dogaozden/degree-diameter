# c3 final push: sample random isometries of V; keep elements of projective order 4, 8, 10 with distinct
# orbit-size profiles (fingerprints). Usage: sample2.py SECONDS SEED OUT.npz
import sys, time, math
from collections import Counter
import numpy as np
from orth import *
secs = float(sys.argv[1]); seed = int(sys.argv[2]); outf = sys.argv[3]
rng = np.random.default_rng(seed)
targets = [4, 8, 10]; KEEP = 6
store = {d: {} for d in targets}
t0 = time.time(); samples = 0
while time.time() - t0 < secs:
    k = int(rng.integers(3, 13))
    g = rand_elem(rng, k)
    perm = perm_of(g)
    cyc = cycles(perm)
    n = 1
    for c in cyc: n = lcm(n, len(c))
    samples += 1
    for d in targets:
        if n % d == 0 and len(store[d]) < 3 * KEEP:
            h = pperm(perm, n // d)
            fp = tuple(sorted(Counter(len(c) for c in cycles(h)).items()))
            if fp not in store[d]:
                store[d][fp] = h
arrays = {}
for d in targets:
    items = list(store[d].items())[:KEEP]
    for j, (fp, h) in enumerate(items):
        arrays[f"d{d}_{j}"] = h
        print(f"d={d} elem {j}: orbit-size profile {fp}", flush=True)
np.savez_compressed(outf, **arrays)
print("samples", samples, "saved", len(arrays), flush=True)
