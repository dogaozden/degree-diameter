# Map mu thresholds to largest group order N per target cell: solve N*exp(-W/N) = mu* (mu is increasing in N).
import math
def W(d, D):
    if D % 2 == 0: return sum(d * (d - 1) ** (2 * i) for i in range(D // 2))
    return 1 + sum(d * (d - 1) ** (2 * i - 1) for i in range(1, (D - 1) // 2 + 1))
def N_of_mu(d, D, mu):
    w = W(d, D); lo, hi = 2.0, w   # mu(N) = N exp(-W/N) is increasing in N (d/dN = exp(-W/N)(1+W/N) > 0), so bisect on [2, W]
    f = lambda N: N * math.exp(-w / N) - mu
    if f(lo) > 0: return None
    for _ in range(200):
        m = (lo * hi) ** 0.5
        if f(m) < 0: lo = m
        else: hi = m
    return (lo * hi) ** 0.5
cells = [(11, 11), (12, 11), (13, 11), (14, 11), (11, 12)]
for d, D in cells:
    out = []
    for mu in (4, 6, 7, 10, 14, 21):
        N = N_of_mu(d, D, mu)
        out.append(f"mu={mu}: N<={N:.3g} (2N<={2*N:.3g})")
    print(f"({d},{D}) W={W(d,D):.4g}: " + "; ".join(out))
