# Level 1: choose the Z_k-parts (J0=0, J1, J2, J3) of S = {e, x, y, z} = generators 0..3 of the dipole4 Haar lift.
# The Z_k-projection of a walk is a homomorphism image, so it depends only on J and k (not on r or m).
# Walks: non-backtracking alternating words s1 s2^-1 s3 ... from (A,e); odd length <= 7 reach side B.
import sys, itertools, numpy as np
k = int(sys.argv[1]); out = sys.argv[2]; maxlen = int(sys.argv[3]) if len(sys.argv) > 3 else 7
words = []  # each word: tuple of generator indices, sign = + at odd positions, - at even
def gen(prefix):
    if prefix: words.append(tuple(prefix))
    if len(prefix) == maxlen: return
    for g in range(4):
        if prefix and prefix[-1] == g: continue
        gen(prefix + [g])
gen([])
odd = [w for w in words if len(w) % 2 == 1]
print("odd walks", len(odd), "all walks", len(words), file=sys.stderr)
# coefficient matrix C[w, g] = sum of signs of positions with generator g
C = np.zeros((len(odd), 4), dtype=np.int64)
for i, w in enumerate(odd):
    for p, g in enumerate(w):
        C[i, g] += 1 if p % 2 == 0 else -1
res = []
Js = list(itertools.product(range(k), repeat=3))  # J1, J2, J3; J0 = 0 WLOG
hist = np.zeros((len(Js), k), dtype=np.int64)
for t, (J1, J2, J3) in enumerate(Js):
    J = np.array([0, J1, J2, J3])
    proj = (C @ J) % k
    hist[t] = np.bincount(proj, minlength=k)
mean = len(odd) / k
for t, (J1, J2, J3) in enumerate(Js):
    h = hist[t]
    if len(set([0, J1, J2, J3])) < 4: continue   # need 4 distinct group elements (a-part may still differ; keep only distinct J for now)
    res.append((int(h.min()), float(((h - mean) ** 2).sum() ** 0.5), J1, J2, J3, h.tolist()))
res.sort(key=lambda r: (-r[0], r[1]))
with open(out, "w") as f:
    for r in res:
        f.write(f"{r[0]} {r[1]:.2f} J={(0,r[2],r[3],r[4])} hist={r[5]}\n")
print("patterns", len(res), "mean per residue", mean, file=sys.stderr)
for r in res[:15]:
    print(r[0], round(r[1], 2), (0, r[2], r[3], r[4]))
