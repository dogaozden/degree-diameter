"""B7 planning script for (11,10): clumped-Poisson mu_A and effort/time predictions, light Python only.
Formulas: W = 11*(1+10^2+10^4+10^6+10^8); lam = W/N; mu = N e^-lam;
mu_A = (mu - F e^-lam)/k + (F-1) e^(-lam/k)  (even D; F = |Fix| incl. e);
evals = 1e5 exp((mu_A-13)/2); sec/eval = c_k * N/75e6 (c_3 = 0.09 s, c_5 = 0.25 s measured at N ~ 75M).
Families: conj SL(2,p), PSL(2,p) x Z_n (k | p-+1, F = torus order, halved for PSL, every prime of n = 1 mod k),
Frobenius of order 5 on SL(2,32) x Z_n (F = 6) and PSL(2,243) x Z_n (F = 12). N in [76M, 80M].
"""
import math, sys

D, DEG = 10, 11
W = DEG * sum((DEG - 1) ** (2 * i) for i in range(D // 2))
assert W == 1111111111, W
LO, HI = 76_000_000, 80_000_000
BUDGET_H = 4.0
CPS = {3: 0.09, 5: 0.25}
N0 = 75_000_000


def is_prime(m):
    if m < 2:
        return False
    i = 2
    while i * i <= m:
        if m % i == 0:
            return False
        i += 1
    return True


def prime_factors(n):
    f, p = [], 2
    while p * p <= n:
        while n % p == 0:
            f.append(p)
            n //= p
        p += 1
    if n > 1:
        f.append(n)
    return f


def n_ok(n, k):
    return all(p % k == 1 for p in prime_factors(n))


def model(N, F, k):
    lam = W / N
    mu = N * math.exp(-lam)
    muA = (mu - F * math.exp(-lam)) / k + (F - 1) * math.exp(-lam / k)
    evals = 1e5 * math.exp((muA - 13) / 2)
    sec = CPS[k] * N / N0
    hours = evals * sec / 3600
    return lam, mu, muA, evals, hours


def m_S(N, F, k, f):
    m = (DEG - f) // k
    return m * math.log(N / k) + max(0, f - 1) * math.log(F) - math.lgamma(m + 1)


rows = []
# conjugation families on SL(2,p), PSL(2,p) x Z_n
for fam in ("SL", "PSL"):
    for k in (3, 5):
        f = DEG % k          # k=3 -> f=2, k=5 -> f=1
        for p in range(5, 700):
            if not is_prime(p):
                continue
            if (p - 1) % k == 0:
                t = p - 1
            elif (p + 1) % k == 0:
                t = p + 1
            else:
                continue
            order = p * (p * p - 1) // (1 if fam == "SL" else 2)
            F = t if fam == "SL" else t // 2
            if order > HI:
                continue
            nlo = -(-LO // order)
            nhi = HI // order
            for n in range(max(1, nlo), nhi + 1):
                N = order * n
                if N < LO or N > HI or not n_ok(n, k):
                    continue
                lam, mu, muA, ev, h = model(N, F, k)
                rows.append(dict(sym="conj", fam=fam, p=p, n=n, k=k, f=f, F=F, N=N, vert=2 * N,
                                 lam=lam, mu=mu, muA=muA, evals=ev, hours=h, lnS=m_S(N, F, k, f)))

# Frobenius of order 5: SL(2,32) x Z_n (F = 6), PSL(2,243) x Z_n (F = 12)
for fam, q0, F in (("SL", 32, 6), ("PSL", 243, 12)):
    order = q0 * (q0 * q0 - 1) // (1 if fam == "SL" else 2)
    k, f = 5, 1
    p = {32: 2, 243: 3}[q0]
    for n in range(max(1, -(-LO // order)), HI // order + 1):
        N = order * n
        if N < LO or N > HI or not n_ok(n, k):
            continue
        lam, mu, muA, ev, h = model(N, F, k)
        rows.append(dict(sym="frob", fam=fam, p=p, n=n, k=k, f=f, F=F, N=N, vert=2 * N,
                         lam=lam, mu=mu, muA=muA, evals=ev, hours=h, lnS=m_S(N, F, k, f)))

rows.sort(key=lambda r: -r["vert"])
out = sys.stdout
print("# all candidates in N in [76M,80M] with prime-factor rule: %d" % len(rows), file=out)

# per-family frontier: largest vertices with predicted hours <= 4
fams = {}
for r in rows:
    key = (r["sym"], r["fam"], r["k"], r["p"] if r["sym"] == "frob" else None)
    fams.setdefault((r["sym"], r["fam"], r["k"]), []).append(r)
print("# per family (sym, group family, k): best feasible (hours <= 4) and smallest infeasible above it", file=out)
for key in sorted(fams, key=lambda x: (x[0], x[2], x[1])):
    rs = sorted(fams[key], key=lambda r: r["vert"])
    feas = [r for r in rs if r["hours"] <= BUDGET_H]
    if not feas:
        print(key, "no feasible candidate in range; smallest hours %.2f at vert %d" % (rs[0]["hours"], rs[0]["vert"]), file=out)
        continue
    best = feas[-1]
    above = [r for r in rs if r["vert"] > best["vert"]]
    nxt = above[0] if above else None
    print(key, "best vert %d (p=%d n=%d F=%d mu=%.2f muA=%.2f evals=%.3g hours=%.2f)" % (
        best["vert"], best["p"], best["n"], best["F"], best["mu"], best["muA"], best["evals"], best["hours"]), file=out)
    if nxt:
        print("    next above: vert %d (p=%d n=%d) hours=%.2f muA=%.2f" % (nxt["vert"], nxt["p"], nxt["n"], nxt["hours"], nxt["muA"]), file=out)

print("# feasible (hours <= 4) candidates, largest first", file=out)
print("%11s %-4s %-5s %5s %6s %3s %4s %4s %7s %6s %6s %9s %7s %6s" % (
    "vertices", "sym", "fam", "p", "n", "k", "f", "F", "N", "mu", "mu_A", "evals", "hours", "lnS-muA"), file=out)
feas_all = [r for r in rows if r["hours"] <= BUDGET_H]
for r in feas_all[:40]:
    print("%11d %-4s %-5s %5d %6d %3d %4d %4d %7d %6.2f %6.2f %9.3g %7.2f %6.1f" % (
        r["vert"], r["sym"], r["fam"], r["p"], r["n"], r["k"], r["f"], r["F"], r["N"], r["mu"], r["muA"],
        r["evals"], r["hours"], r["lnS"] - r["muA"]), file=out)
print("# count feasible: %d of %d" % (len(feas_all), len(rows)), file=out)
