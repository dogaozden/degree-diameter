"""B7: raw clumped-model predictions (card formulas) and class-saturation-corrected predictions for (11,10).
Raw: lam = W/N, mu = N e^-lam, mu_A = (mu - F e^-lam)/k + (F-1) e^(-lam/k), evals = 1e5 exp((mu_A-13)/2),
sec/eval = c_k N/75e6 (c_3 = 0.09, c_5 = 0.25). Corrected: lam -> lam_eff = lam (1-e^-x)/x, x = W/(K'_k |H|) (see plan_b7_struct.py),
everything else the same. Families as in plan_b7.py. Light Python only.
"""
import math, sys
from math import comb
W = 1111111111
LO, HI = 76_000_000, 80_000_000
CPS = {3: 0.09, 5: 0.25}; N0 = 75e6; BUD = 4.0
Kp = {3: sum(2 ** j * comb(9, j) * comb(9, j) for j in range(10)),
      5: sum(2 ** j * comb(10, j) * comb(9, j) for j in range(10))}


def is_prime(m):
    return m >= 2 and all(m % i for i in range(2, int(m ** 0.5) + 1))


def pf(n):
    f, p = [], 2
    while p * p <= n:
        while n % p == 0:
            f.append(p); n //= p
        p += 1
    if n > 1: f.append(n)
    return f


def est(N, F, k, H):
    lam = W / N
    x = W / (Kp[k] * H)
    lam_e = lam * (1 - math.exp(-x)) / x
    out = {}
    for tag, L in (("raw", lam), ("corr", lam_e)):
        mu = N * math.exp(-L)
        muA = (mu - F * math.exp(-L)) / k + (F - 1) * math.exp(-L / k)
        ev = 1e5 * math.exp(min((muA - 13) / 2, 700))
        out[tag] = (mu, muA, ev, ev * CPS[k] * N / N0 / 3600)
    return lam, x, out


rows = []
for fam in ("SL", "PSL"):
    for k in (3, 5):
        for p in range(5, 700):
            if not is_prime(p): continue
            if (p - 1) % k == 0: t = p - 1
            elif (p + 1) % k == 0: t = p + 1
            else: continue
            order = p * (p * p - 1) // (1 if fam == "SL" else 2)
            F = t if fam == "SL" else t // 2
            for n in range(max(1, -(-LO // order)), HI // order + 1):
                N = order * n
                if N < LO or N > HI or any(q % k != 1 for q in pf(n)): continue
                rows.append(("conj", fam, p, n, k, F, N, order))
for fam, q0, F, p in (("SL", 32, 6, 2), ("PSL", 243, 12, 3)):
    order = q0 * (q0 * q0 - 1) // (1 if fam == "SL" else 2)
    for n in range(max(1, -(-LO // order)), HI // order + 1):
        N = order * n
        if N < LO or N > HI or any(q % 5 != 1 for q in pf(n)): continue
        rows.append(("frob", fam, p, n, 5, F, N, order))

res = []
for sym, fam, p, n, k, F, N, H in rows:
    lam, x, o = est(N, F, k, H)
    res.append(dict(sym=sym, fam=fam, p=p, n=n, k=k, F=F, N=N, H=H, lam=lam, x=x, raw=o["raw"], corr=o["corr"]))

print("K'_3 = %d, K'_5 = %d" % (Kp[3], Kp[5]))
print("# families: best (largest vertices) with predicted hours <= 4 h, raw and corrected")
for key in sorted({(r["sym"], r["fam"], r["k"]) for r in res}):
    rs = sorted([r for r in res if (r["sym"], r["fam"], r["k"]) == key], key=lambda r: r["N"])
    for tag in ("raw", "corr"):
        feas = [r for r in rs if r[tag][3] <= BUD]
        if feas:
            b = feas[-1]
            print(key, tag, "vert %d p=%d n=%d |H|=%d x=%.3f mu=%.1f muA=%.2f evals=%.3g h=%.2f" % (
                2 * b["N"], b["p"], b["n"], b["H"], b["x"], b["raw"][0] if tag == "raw" else b["corr"][0], b[tag][1], b[tag][2], b[tag][3]))
        else:
            m = rs[0]
            print(key, tag, "none <= 4 h in range; smallest-N option vert %d p=%d n=%d hours=%.2f" % (
                2 * m["N"], m["p"], m["n"], m[tag][3]))
print()
print("# corrected ranking: runs with corrected hours <= 4, largest vertices first (x <= 0.03 marked safe)")
print("%11s %-6s %4s %6s %3s %4s %10s %7s %6s %6s %8s %9s %7s %8s" % ("vertices", "group", "p", "n", "k", "F", "N", "mu_raw", "mu_A_raw", "x", "mu_A_corr", "evals_c", "hours_c", "safe"))
feas = sorted([r for r in res if r["corr"][3] <= BUD], key=lambda r: -r["N"])
for r in feas[:25]:
    name = ("%s(2,%d)" % (r["fam"], r["p"]) if r["sym"] == "conj" else "%s(2,%d)[frob]" % (r["fam"], {"SL": 32, "PSL": 243}[r["fam"]]))
    print("%11d %-6s %4d %6d %3d %4d %10d %7.1f %6.2f %6.3f %8.2f %9.3g %7.2f %8s" % (
        2 * r["N"], name, r["p"], r["n"], r["k"], r["F"], r["N"], r["raw"][0], r["raw"][1], r["x"], r["corr"][1],
        r["corr"][2], r["corr"][3], "yes" if r["x"] <= 0.03 else "no"))
print("# raw ranking (card model, no correction), top 12 feasible")
feas = sorted([r for r in res if r["raw"][3] <= BUD], key=lambda r: -r["N"])
for r in feas[:12]:
    name = ("%s(2,%d)" % (r["fam"], r["p"]) if r["sym"] == "conj" else "%s(2,%d)[frob]" % (r["fam"], {"SL": 32, "PSL": 243}[r["fam"]]))
    print("%11d %-6s %4d %6d %3d %4d %10d mu=%.1f muA=%.2f x=%.3f hours=%.2f" % (2 * r["N"], name, r["p"], r["n"], r["k"], r["F"], r["N"], r["raw"][0], r["raw"][1], r["x"], r["raw"][3]))
print("# structure-safe (x <= 0.03) raw ranking, top 12 feasible")
feas = sorted([r for r in res if r["raw"][3] <= BUD and r["x"] <= 0.03], key=lambda r: -r["N"])
for r in feas[:12]:
    name = ("%s(2,%d)" % (r["fam"], r["p"]) if r["sym"] == "conj" else "%s(2,%d)[frob]" % (r["fam"], {"SL": 32, "PSL": 243}[r["fam"]]))
    print("%11d %-6s %4d %6d %3d %4d %10d mu=%.1f muA=%.2f x=%.3f hours=%.2f evals=%.3g" % (2 * r["N"], name, r["p"], r["n"], r["k"], r["F"], r["N"], r["raw"][0], r["raw"][1], r["x"], r["raw"][3], r["raw"][2]))
