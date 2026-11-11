"""cellstats.py d D 2N : bipartite Moore bound M_b, the M_b - 6 upper bound used in BEYOND_TABLE, % of M_b,
size-law mu = N exp(-W/N) with W = sum over odd j <= D-1 (even D) of d (d-1)^(j-1), and the 2N where mu = 5."""
import math, sys
def W(d, D):
    if D % 2 == 0: return sum(d * (d - 1) ** (j - 1) for j in range(1, D, 2))
    return 1 + sum(d * (d - 1) ** (j - 1) for j in range(2, D, 2))
def stats(d, D, V):
    Mb = 2 * sum((d - 1) ** i for i in range(D)); N = V // 2; w = W(d, D)
    mu = N * math.exp(-w / N)
    lo, hi = 1.0, float(Mb)
    for _ in range(200):
        m = (lo + hi) / 2
        if m * math.exp(-w / m) < 5: lo = m
        else: hi = m
    return Mb, Mb - 6, 100.0 * V / Mb, mu, 2 * lo
if __name__ == "__main__":
    d, D, V = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    Mb, ub, pct, mu, sl = stats(d, D, V)
    print(f"({d},{D}) value {V:,} M_b {Mb:,} upper {ub:,} pct {pct:.2f} mu {mu:.2f} sizelaw2N(mu=5) {sl:.3g}")
