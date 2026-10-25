#!/usr/bin/env python3
"""rule.py: the corrected symmetry rule of ORDER2.md section 4, as a calculator.

Input: a cell (d = Delta, D), N = |G|, the symmetry's order k, and for every subgroup H of <alpha> the number of
elements whose stabiliser is exactly H (given as |Fix(H)| for the cyclic subgroups, nested), plus |Anti(beta)| for
the involution beta in <alpha> when k is even.  Output:
  mu       = N exp(-W/N)                                   (haar_sym's mu; W = binding words)
  generic  = mu / k  (even D),  mu / k  (odd D: clumps of 2k over two sides = mu/k as well)
  fixed    = sum over H != 1 of  #{Stab = H} (|H|/|A|) exp(-lambda/|H|)  * sides
  anti     = odd D only: |Anti(beta) minus Fix| (2/k) exp(-lambda/2)   (beta* = inversion o beta fixes Anti; ORDER2 3.3)
  twisted relators of beta (k even): R_j = rho d (d-1)^(2j-1) / (4j),  rho = |Anti|/N, each costing a fraction
           c_j = 2j (l - 2j + 1) / (d (d-1)^(2j-1)) of the binding words (l = D - 1); avoidable when R_j <= AVOID,
           unavoidable otherwise; the unavoidable ones multiply mu_A by exp(lambda * sum R_j c_j)
  mu_A     = (generic + fixed + anti) * penalty
  evals    = effort law of SIZE_LAW / BEYOND_RANDOM:  1e5 exp((mu_A - 13)/2)   (scatter about a factor 5)
Run without arguments for the worked table of ORDER2.md (every row's class sizes are in the CASES list below, each
with its source: haar_sym's |Fix| line, twist.py/targets.py counts, or the closed forms of ORDER2 2.2).
"""
import math, sys

AVOID = 5.0     # a relator family with Poisson mean <= AVOID is treated as avoidable by the search


def words(d, D):
    """haar_sym's Wwords: binding words of one side."""
    if D % 2:
        k = (D - 1) // 2
        return 1 + sum(d * (d - 1) ** (2 * i - 1) for i in range(1, k + 1))
    k = D // 2
    return sum(d * (d - 1) ** (2 * i) for i in range(k))


def palindromes(d, D):
    """sigma-palindromic A-words of even length <= D - 1 (odd D, no fixed letters): ORDER2.md 2.8."""
    return sum(d * (d - 1) ** (j - 1) for j in range(1, (D - 1) // 2 + 1))


def rule(d, D, N, k, stab, anti=0, avoid=AVOID, verbose=False, fixb=None):
    """stab: dict {|H|: number of elements with stabiliser of order |H| in <alpha>} for |H| > 1 (cyclic <alpha>,
    so a subgroup is determined by its order).  anti: |Anti(beta)| minus its intersection with Fix (k even).
    fixb: |Fix(beta)| of the involution beta (odd D): the palindromic words land on Im L, |Im L| = N/|Fix(beta)|,
    giving each of its elements pi = P |Fix(beta)| / N single shots (ORDER2.md 2.8, 3.5).  Without fixb the first
    session's term (2/k) |Anti| e^(-lambda/2) is used."""
    W = words(d, D)
    lam = W / N
    mu = N * math.exp(-lam)
    sides = 2 if D % 2 else 1
    generic = mu / k
    # formula (1) of BEYOND_RANDOM: sides * sum_x |Stab(x)|/|A| exp(-lambda/|Stab(x)|), |A| = k (even D), 2k (odd D,
    # with inversion); for x fixed by H <= <alpha> this is |H|/k exp(-lambda/|H|) at both parities
    fixed = 0.0
    for h, cnt in stab.items():
        fixed += cnt * (h / k) * math.exp(-lam / h)
    # odd D: x in Anti(beta) is fixed by beta* = inversion o beta (stabiliser of order 2 in A): 2/k exp(-lambda/2) each
    anti_cost = (2.0 / k) * anti * math.exp(-lam / 2) if (D % 2 and k % 2 == 0) else 0.0
    anti_old = anti_cost
    if D % 2 and k % 2 == 0 and anti and fixb:
        img = min(anti, N / fixb)
        pi = palindromes(d, D) * fixb / N
        anti_cost = (2.0 / k) * (img * math.exp(-lam / 2 - pi) + (anti - img) * math.exp(-lam / 2))
    ell = D - 1
    rel = []
    pen = 0.0
    gf = 0.0
    mu0 = generic + fixed + anti_cost
    if k % 2 == 0 and anti:
        rho = anti / N
        for j in range(1, (ell - 1) // 2 + 1 if ell % 2 else ell // 2):
            R = rho * d * (d - 1) ** (2 * j - 1) / (4 * j)
            c = 2 * j * (ell - 2 * j + 1) / (d * (d - 1) ** (2 * j - 1))
            unav = R > avoid
            if unav:
                pen += R * c
            # Poisson generating function: summing over n ~ Poisson(R) with weight exp(-mu0 e^{lambda c n}) gives an
            # added R (1 - e^{-x}) nats, x = mu0 lambda c, and n* = R e^{-x} cycles in a typical solution
            x = mu0 * lam * c
            gf += R * (1 - math.exp(-x))
            rel.append((4 * j, R, c, unav, R * math.exp(-x)))
    penalty = math.exp(lam * pen)
    muA = mu0 * penalty
    evals = 1e5 * math.exp((muA - 13) / 2)
    out = dict(lam=lam, mu=mu, generic=generic, fixed=fixed, anti=anti_cost, anti_old=anti_old, penalty=penalty, muA=muA, evals=evals,
               mu0=mu0, gf=gf, evals0=1e5 * math.exp((mu0 - 13) / 2), relators=rel)
    return out


# Worked cases.  stab = {order of stabiliser: count}; anti = |Anti(beta)| outside Fix(beta).
# Sources: (h) haar_sym/haar_order2 log line "|Fix(alpha)| = ...", (t) targets.py class sizes, (f) closed forms.
CASES = [
    # name, d, D, N, k, stab {|H|: count}, anti (outside Fix), source of the class sizes, observed
    # (6,8): the order-2 winners and the failures the earlier rule was built on
    ("(6,8) PSL(2,11)xZ24, conj order 2, r=11", 6, 8, 15840, 2, {2: 24}, 656, "h,t", "solved 3.3e5 (table-squad); 8.8e6 best 2 (here)"),
    ("(6,8) PSL(2,11)xZ24, conj order 2, r=23", 6, 8, 15840, 2, {2: 24}, 1320, "t", "RANDORB p1 61 vs 30 (r=11)"),
    ("(6,8) SL(2,25), conj order 2", 6, 8, 15600, 2, {2: 24}, 648, "h,t", "solved 2.1e6 (table-squad)"),
    ("(6,8) SL(2,25), Frobenius order 2", 6, 8, 15600, 2, {2: 120}, 128, "t", "-"),
    ("(6,8) SL(2,8)xZ32, conj order 2", 6, 8, 16128, 2, {2: 16}, 1008, "h,f", "best 7-12, 10 seeds x 2.4e6"),
    ("(6,10) SL(2,31)xZ9, conj order 2", 6, 10, 267840, 2, {2: 32}, 8370 - 32, "h,f", "best 12 at 1.4e6"),
    ("(7,8) SL(2,13)xZ19, conj order 2, z->-z", 7, 8, 41496, 2, {2: 12}, 182 * 19 - 12, "f", "RANDORB median 458 vs 31 random (STRUCTURE)"),
    ("(7,8) PSL(2,23)xZ8, conj order 2 (f=1)", 7, 8, 48576, 2, {2: 48}, 1008, "h,f", "best 13 at 5.8e6"),
    ("(7,8) PSL(2,19)xZ14, conj order 3 (record)", 7, 8, 47880, 3, {3: 17}, 0, "h", "solved 2.6e5 (STRUCTURE)"),
    ("(8,8) PSL(2,7)xSL(2,9), conj order 2", 8, 8, 120960, 2, {2: 64}, 1980 - 64, "h,f", "best 7-12 at 2-9e5"),
    ("(8,8) PSL(2,17)xZ49, conj order 3 (record)", 8, 8, 119952, 3, {3: 8}, 0, "h", "solved 8.8e4 (STRUCTURE)"),
    ("(9,8) PSL(2,41)xZ8, conj order 2 (f=1)", 9, 8, 275520, 2, {2: 80}, 3448 - 80, "h,f", "best 18 at 1.9e5"),
    # (13,8): order 6 against order 3 on the record group, and the record attempts
    ("(13,8) SL(2,64)xZ13, conj order 3", 13, 8, 3407040, 3, {3: 63}, 0, "h", "solved 1.7e5 (BEYOND_RANDOM)"),
    ("(13,8) SL(2,64)xZ13, Frobenius order 3", 13, 8, 3407040, 3, {3: 60}, 0, "h", "best 1 at 2.6e5 (BEYOND_RANDOM)"),
    ("(13,8) SL(2,64)xZ13, Frobenius order 6", 13, 8, 3407040, 6, {6: 6, 3: 54, 2: 498}, 520 * 13 - 6, "h,f", "solved 4.7e3, 9.6e3, 3.7e4 (here)"),
    ("(13,8) SL(2,7)^2xZ31, swap-conj order 6", 13, 8, 3499776, 6, {6: 6, 3: 30, 2: 330}, 112896 * 31 // 336 - 6, "h,f", "see ORDER2.md"),
    ("(13,8) SL(2,8)^2xZ14, swap-Frobenius order 6", 13, 8, 3556224, 6, {6: 12, 3: 60, 2: 996}, 504 * 14 - 12, "h,f", "best 18 at 6.3e4 (here)"),
    ("(13,8) SL(2,64)xZ14, Frobenius order 6", 13, 8, 3669120, 6, {6: 12, 3: 108, 2: 996}, 520 * 14 - 12, "h,f", "not run"),
    # odd D: the Anti targets
    ("(6,9) SL(2,25)xZ4, conj order 2", 6, 9, 62400, 2, {2: 48}, 2596, "t", "Anti missed at 0.7-0.85 sqrt(p)"),
    ("(6,9) SL(2,25)xZ4, Frobenius order 2", 6, 9, 62400, 2, {2: 240}, 516, "t", "Anti missed at 0.5-0.7 sqrt(p)"),
    ("(6,9) SL(2,25)xZ4, random S", 6, 9, 62400, 1, {}, 0, "-", "-"),
    ("(6,9) SL(2,3)xSL(2,7)xZ8, conj order 2", 6, 9, 64512, 2, {2: 64}, 64512 // 64 * 2, "h; anti assumed 2N/|Fix|", "best 36 at 2.8e6"),
    ("(6,7) PSL(2,11)xZ7, conj order 2", 6, 7, 4620, 2, {2: 12}, 56 * 7 - 12, "h,f", "best 51 at 1.9e7"),
    ("(7,9) SL(2,31)xZ8, conj order 2 (f=1)", 7, 9, 238080, 2, {2: 64}, 930 * 4 - 64, "h,f", "best 76 at 1.2e6"),
]


# Second session (ORDER2.md 3.5, 5.5): odd-D screens, with |Fix(beta)| for the palindrome term.  Observed = lower
# tail of random symmetric S in clumps (cost / 2k at odd D), from runs/r2/ro127_*.log, ro149_*.log, ro159_*.log.
# name, d, D, N, k, stab, anti (outside Fix), fixb = |Fix(beta)|, observed
CASES2 = [
    ("(6,9) SL(2,25)xZ4, conj order 2", 6, 9, 62400, 2, {2: 48}, 2596, 48, "Anti missed at 0.69-0.85 sqrt(p)"),
    ("(6,9) SL(2,25)xZ4, Frobenius order 2", 6, 9, 62400, 2, {2: 240}, 516, 240, "Anti missed at 0.48-0.70 sqrt(p)"),
    ("(12,7) SL(2,64), Frobenius order 6", 12, 7, 262080, 6, {6: 6, 3: 54, 2: 498}, 456, 504, "p1 41.7, p10 57.6 clumps"),
    ("(12,7) SL(2,64), Frobenius order 3", 12, 7, 262080, 3, {3: 59}, 0, None, "p1 75.2, p10 92.8"),
    ("(12,7) SL(2,64), conjugation order 3", 12, 7, 262080, 3, {3: 62}, 0, None, "p1 79.5, p10 98.3"),
    ("(12,7) SL(2,64), Frobenius order 2", 12, 7, 262080, 2, {2: 503}, 456, 504, "p1 144.5, p10 180"),
    ("(12,7) SL(2,64), random S", 12, 7, 262080, 1, {}, 0, None, "p1 247 (2-element clumps)"),
    ("(12,7) SL(2,8)^2, swap-conj order 6", 12, 7, 254016, 6, {6: 9, 3: 72, 2: 495}, 440, 504, "p1 35.6, p10 50.3"),
    ("(12,7) SL(2,8)^2, conj order 3", 12, 7, 254016, 3, {3: 80}, 0, None, "p1 69.3, p10 87.5"),
    ("(12,7) SL(2,8)^2, swap order 2", 12, 7, 254016, 2, {2: 503}, 440, 504, "p1 118, p10 153"),
    ("(15,9) SL(2,64)xZ403, Frobenius order 6, 6+6+3", 15, 9, 105618240, 6, {6: 6, 3: 54, 2: 6546}, 16056, 6552, "min 3.2, p10 6.3 clumps (16 samples)"),
    ("(15,9) SL(2,64)xZ403, Frobenius order 3", 15, 9, 105618240, 3, {3: 59}, 0, None, "min 10.3, p10 13.8 (16 samples)"),
]


def main2():
    print("second session (ORDER2.md 3.5, 5.5): odd D, mu_A0 = mu/k + fixed + anti, anti with the palindrome term;")
    print("anti_old = the first session's (2/k)|Anti|e^(-lambda/2)")
    print(f"{'case':52s} {'lam':>5s} {'mu':>6s} {'mu/k':>6s} {'fixed':>6s} {'anti_old':>8s} {'anti':>6s} {'mu_A0':>6s} {'evals0':>8s}  | observed")
    for name, d, D, N, k, stab, anti, fixb, obs in CASES2:
        r = rule(d, D, N, k, stab, anti, fixb=fixb)
        print(f"{name:52s} {r['lam']:5.2f} {r['mu']:6.1f} {r['generic']:6.2f} {r['fixed']:6.2f} {r['anti_old']:8.2f} {r['anti']:6.2f} {r['mu0']:6.1f} {r['evals0']:8.2g}  | {obs}")


def main():
    print(f"{'case':52s} {'lam':>5s} {'mu':>6s} {'mu/k':>6s} {'fixed':>6s} {'anti':>6s} {'pen':>5s} {'mu_A':>6s} {'evals':>8s} {'evals0':>8s} {'gfnat':>5s}  | observed")
    print("  mu_A = (mu/k + fixed + anti) x pen; evals from mu_A (penalised) and evals0 from mu_A without the twisted-cycle")
    print("  penalty; gfnat = sum_j R_j (1 - exp(-mu_A0 lam c_j)), the first-moment cost of twisted cycles in nats")
    for name, d, D, N, k, stab, anti, src, obs in CASES:
        r = rule(d, D, N, k, stab, anti)
        rel = "; ".join(f"{L}: R={R:.2g} c={c:.2g} n*={ns:.2g}{' U' if u else ''}" for L, R, c, u, ns in r["relators"])
        print(f"{name:52s} {r['lam']:5.2f} {r['mu']:6.1f} {r['generic']:6.2f} {r['fixed']:6.2f} {r['anti']:6.2f} {r['penalty']:5.2f} {r['muA']:6.1f} {r['evals']:8.2g} {r['evals0']:8.2g} {r['gf']:5.1f}  | {obs}")
        print(f"{'':52s}   twisted cycles (length: Poisson mean R, word fraction c, n* = expected in a solution, U = above R*): {rel or '-'}")


if __name__ == "__main__":
    if sys.argv[1:] == ["--second"]:
        main2()
    else:
        main()
