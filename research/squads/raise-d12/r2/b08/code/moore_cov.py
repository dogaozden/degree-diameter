# For random abelian voltages phi in Z_n^64 on the H(2) base: fraction of (point 0, line L) pairs whose 65 walk
# residues cover all of Z_n; compare with the independent-uniform model P(65 balls cover n bins).
import random, math
from collections import Counter
import moore
W = [w for w in moore.walks_from(0) if w[0] >= 63 and w[1] <= 11]
lines = sorted(set(w[0] for w in W))
by_line = {L: [w[2] for w in W if w[0] == L] for L in lines}
def covered_all(n, phi):
    ok = 0
    for L in lines:
        s = set()
        for vec in by_line[L]:
            s.add(sum(sg * phi[c] for c, sg in vec) % n)
        if len(s) == n: ok += 1
    return ok
def indep_cover(n, m=65):
    # P(m iid uniform balls cover all n bins), by inclusion-exclusion
    return sum((-1)**j * math.comb(n, j) * ((n - j) / n) ** m for j in range(n + 1))
random.seed(1)
for n in (6, 8, 10, 11, 13, 17):
    trials = 300
    frac_pairs = 0.0; full_phi = 0
    for _ in range(trials):
        phi = [random.randrange(n) for _ in range(moore.NC)]
        c = covered_all(n, phi)
        frac_pairs += c / len(lines)
        if c == len(lines): full_phi += 1
    print(f"n={n}: fraction of point-line pairs covered {frac_pairs/trials:.4f}; P(all 63 lines covered) {full_phi/trials:.3f}; indep model per-pair P(cover) {indep_cover(n):.4f}", flush=True)
