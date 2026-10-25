#!/usr/bin/env python3
"""Card c8 (squad d15D10-r2): does cost correlate with A(S) = max_{xi=1..n-1} |(1/15) sum_i exp(2 pi i xi z_i / n)|?

Input: the "ZS cost=<cost> z=<z_0> ... <z_14>" lines written by haar_lean_z (RANDORB mode).
Usage: python3 analyze_z.py ZSFILE N K LAM CSVOUT
  N   = modulus n of Z_n (the z-parts live in Z_n)
  K   = orbit size k (ORBIT="k m 0"); used only for the orbit sanity check (z of orbit j = indices k*j .. k*j+k-1)
  LAM = lambda used for the predicted factor I0(2*LAM*A^9); 12.9 for the (15,8) proxy, 17.6 for (15,10)
  CSVOUT = per-sample table (idx, cost, A, predicted factor)
Prints Spearman correlation (average ranks for ties, bootstrap 95% CI, normal-approx p) of cost with A, quartile medians,
and a decile table. The predicted factor is monotone in A, so its rank correlation equals that of A.
"""
import csv
import math
import re
import sys

import numpy as np

PAT = re.compile(r"^ZS cost=(-?\d+) z=(.*)$")


def parse(path):
    rows = []
    with open(path) as f:
        for line in f:
            m = PAT.match(line.strip())
            if m:
                rows.append((int(m.group(1)), [int(x) for x in m.group(2).split()]))
    return rows


def A_of(z, n):
    """max over xi = 1..n-1 of |(1/15) sum_i exp(2 pi i xi z_i / n)| via the FFT of the z-histogram."""
    h = np.bincount(np.asarray(z) % n, minlength=n).astype(float)
    F = np.fft.fft(h)                       # F[k] = sum_i exp(-2 pi i k z_i / n); k -> -k permutes 1..n-1
    return float(np.max(np.abs(F[1:n])) / len(z))


def rankdata(x):
    x = np.asarray(x, dtype=float)
    order = np.argsort(x, kind="mergesort")
    xs = x[order]
    ranks = np.empty(len(x))
    i = 0
    while i < len(x):
        j = i
        while j + 1 < len(x) and xs[j + 1] == xs[i]:
            j += 1
        ranks[order[i:j + 1]] = 0.5 * (i + j) + 1.0
        i = j + 1
    return ranks


def spearman(x, y):
    rx = rankdata(x)
    ry = rankdata(y)
    rx -= rx.mean()
    ry -= ry.mean()
    den = math.sqrt(float((rx * rx).sum()) * float((ry * ry).sum()))
    return float((rx * ry).sum() / den) if den > 0 else float("nan")


def p_normal(r, n):
    """two-sided p for Spearman r via t = r sqrt((n-2)/(1-r^2)) and the normal tail (fine for n ~ 1000)."""
    if abs(r) >= 1:
        return 0.0
    t = r * math.sqrt((n - 2) / (1 - r * r))
    return math.erfc(abs(t) / math.sqrt(2))


def main():
    path, n, k, lam, csvout = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4]), sys.argv[5]
    rows = parse(path)
    if not rows:
        sys.exit("no ZS lines in " + path)
    cost = np.array([c for c, _ in rows], dtype=float)
    A = np.array([A_of(z, n) for _, z in rows])
    f = np.i0(2.0 * lam * A ** 9)           # predicted factor on the uncovered count
    nz = len(rows[0][1])
    print("file=%s samples=%d n=%d k=%d z-count=%d lambda=%.2f" % (path, len(rows), n, k, nz, lam))

    # orbit sanity check: z[k j + i] = AR^i z[k j] mod n for one AR shared by all orbits
    ar_hits = {}
    for _, z in rows:
        if z[0] % n:
            ar = (z[1] * pow(z[0], -1, n)) % n if math.gcd(z[0], n) == 1 else None
            if ar is not None:
                ar_hits[ar] = ar_hits.get(ar, 0) + 1
    if ar_hits:
        ar_best = max(ar_hits, key=ar_hits.get)
        ok = 0
        tot = 0
        for _, z in rows:
            for j in range(nz // k):
                base = z[k * j]
                for i in range(k):
                    tot += 1
                    ok += int(z[k * j + i] % n == (pow(ar_best, i, n) * base) % n)
        print("orbit check: AR=%d (most common ratio z1/z0), z[kj+i] == AR^i z[kj] for %d of %d entries" % (ar_best, ok, tot))

    print("A: min=%.4f p10=%.4f median=%.4f p90=%.4f max=%.4f mean=%.4f" % (
        A.min(), np.percentile(A, 10), np.median(A), np.percentile(A, 90), A.max(), A.mean()))
    print("cost: min=%d median=%.1f mean=%.2f max=%d distinct=%d" % (
        cost.min(), np.median(cost), cost.mean(), cost.max(), len(set(cost.tolist()))))

    rho = spearman(cost, A)
    rng = np.random.default_rng(12345)
    boots = []
    for _ in range(2000):
        idx = rng.integers(0, len(cost), len(cost))
        boots.append(spearman(cost[idx], A[idx]))
    lo, hi = np.percentile(boots, [2.5, 97.5])
    print("SPEARMAN cost vs A: rho=%.4f  bootstrap95=[%.4f, %.4f]  p(normal approx)=%.3g" % (
        rho, lo, hi, p_normal(rho, len(cost))))
    print("SPEARMAN cost vs predicted factor I0(2*%.1f*A^9): rho=%.4f (identical ranking)" % (lam, spearman(cost, f)))

    q1, q3 = np.percentile(A, 25), np.percentile(A, 75)
    lowm, highm = A <= q1, A >= q3
    print("quartiles of A: Q1=%.4f Q3=%.4f  n_low=%d n_high=%d" % (q1, q3, lowm.sum(), highm.sum()))
    med_lo, med_hi = np.median(cost[lowm]), np.median(cost[highm])
    print("median cost lowest A quartile = %.1f (mean %.2f, mean f %.3f)" % (med_lo, cost[lowm].mean(), f[lowm].mean()))
    print("median cost highest A quartile = %.1f (mean %.2f, mean f %.3f)" % (med_hi, cost[highm].mean(), f[highm].mean()))
    print("ratio high/low: median cost %.3f, mean cost %.3f, mean predicted factor %.3f" % (
        med_hi / med_lo if med_lo else float("nan"), cost[highm].mean() / cost[lowm].mean(),
        f[highm].mean() / f[lowm].mean()))
    print("deciles of A (count, mean A, median cost, mean cost, mean f):")
    edges = np.percentile(A, np.arange(0, 101, 10))
    for b in range(10):
        m = (A >= edges[b]) & ((A <= edges[b + 1]) if b == 9 else (A < edges[b + 1]))
        if m.sum():
            print("  D%d  n=%4d  A=%.3f  median cost=%6.1f  mean cost=%7.2f  mean f=%8.3f" % (
                b + 1, m.sum(), A[m].mean(), np.median(cost[m]), cost[m].mean(), f[m].mean()))

    with open(csvout, "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["idx", "cost", "A", "pred_factor"])
        for i in range(len(cost)):
            w.writerow([i, int(cost[i]), "%.6f" % A[i], "%.6f" % f[i]])
    print("per-sample table: %s" % csvout)


if __name__ == "__main__":
    main()
