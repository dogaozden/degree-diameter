# Which order-4 isometries of V = {x4 = -x0} (q = 11) give 240-point orbit packings? For random g, take h = g^(n/4)
# (projective order 4), record kernel dimensions of h - 1, h + 1, h^2 + 1 (after scaling h^4 = 1 when possible) and the
# orbitclique result (10 s). Usage: python3 class4.py SAMPLES SEED
import sys, subprocess, os
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d14D7-r3/c3')
from orth import *
ns = int(sys.argv[1]); seed = int(sys.argv[2]); rng = np.random.default_rng(seed)
def mpow(A, k):
    R = np.eye(6, dtype=np.int64); B = A.copy()
    while k:
        if k & 1: R = (R @ B) % p
        B = (B @ B) % p; k >>= 1
    return R
def rank(A):
    A = A.copy() % p; r = 0; rows, cols = A.shape
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if A[i, c]: piv = i; break
        if piv is None: continue
        A[[r, piv]] = A[[piv, r]]; A[r] = (A[r] * INV[A[r, c]]) % p
        for i in range(rows):
            if i != r and A[i, c]: A[i] = (A[i] - A[i, c] * A[r]) % p
        r += 1
    return r
I = np.eye(6, dtype=np.int64); seen = {}
done = 0
while done < ns:
    g = rand_elem(rng, int(rng.integers(3, 13)))
    perm = perm_of(g); cyc = cycles(perm); n = 1
    for c in cyc: n = lcm(n, len(c))
    if n % 4: continue
    h = mpow(g, n // 4)
    h4 = mpow(h, 4); lam = h4[0, 0]
    if not np.array_equal(h4, (lam * I) % p): continue
    # scale so that h^4 = 1 if lam is a 4th power
    sc = [s for s in range(1, p) if pow(s, 4, p) == lam]
    if sc: h = (h * INV[sc[0]]) % p
    k1 = 6 - rank((h - I) % p); km1 = 6 - rank((h + I) % p); ki = 6 - rank((mpow(h, 2) + I) % p)
    hp = perm_of(h)
    prof = tuple(sorted({len(c) for c in cycles(hp)}))
    key = (bool(sc), k1, km1, ki, prof)
    if seen.get(key, 0) >= 2: continue
    seen[key] = seen.get(key, 0) + 1
    fn = f"c4perm_{seed}_{done}.txt"; np.savetxt(fn, hp, fmt='%d')
    r = subprocess.run(['nice', '-n', '5', '../orbitclique', '../../data/E11.map', fn, '10', '1', f'flags/c4_{seed}_{done}.flags'], capture_output=True, text=True)
    best = [l for l in r.stderr.splitlines() if l.startswith('best')]
    print("scaled" if sc else "unscaled(h^4=%d)" % lam, "dims ker(h-1),ker(h+1),ker(h^2+1) =", k1, km1, ki, "cycle lengths", prof, "->", best[0] if best else r.stderr[-200:], flush=True)
    np.save(f"c4mat_{seed}_{done}.npy", h)
    done += 1
