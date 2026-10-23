"""BEYOND_RANDOM.md §4: which symmetry group A should help most, per cell, by the clumped Poisson model.
Run from this folder: python3 symmetry_options.py   (output: symmetry_options_out.txt)

For each cell and each candidate (group Q x Z_n near the current record, symmetry A acting on it) it computes

    mu_A = sides * sum over stabiliser types H <= A of  #{x : Stab(x) = H} * (|H|/|A|) * w * exp(-lambda_eff / |H|),

(w = 1/2 per side at odd D, inverse pairs; 1 at even D) and the search effort the random-S effort law predicts,
evals ~ 1e5 exp((mu_A - 13)/2) (BEYOND_RANDOM §3 shows the orbit runs follow it). Two penalties are included:
  * involutive elements beta of A force same-length coincidences v = beta(v)^-1 on even-length subwords whenever
    v is in Anti(beta) = {u : beta(u) = u^-1}, density rho >= 1/|Fix(beta)| (the map x -> x^-1 beta(x) is
    |Fix|-to-1 into Anti). Expected fraction of binding words lost: delta = rho * l^2 / 8 (l = D - 1).
    We use rho = 1/|Fix(beta)| (tight for conjugation in SL(2,q)).
  * order-k (k odd) symmetries force only length-changing coincidences (2j vs 2(k-j) letters), which cost
    O(Delta^-4) of the words: ignored.
Fixed generators are taken as f <= 2 (f = 0 allowed), never 3: three elements of an abelian Fix(alpha) always
satisfy x y^-1 z = z y^-1 x (BEYOND_RANDOM §2)."""
import math
from math import gcd
from model import W, W_eff
from groups_inv import sl2, psl2, cyc, prod

def is_pp(q):
    for p in range(2, int(q ** 0.5) + 2):
        if q % p == 0:
            e = 0
            while q % p == 0: q //= p; e += 1
            return (p, e) if q == 1 else None
    return (q, 1) if q > 1 else None

def primes(n):
    out, p = [], 2
    while p * p <= n:
        while n % p == 0: out.append(p); n //= p
        p += 1
    if n > 1: out.append(n)
    return out

def fixz(n, k):
    """fewest fixed points of z -> r z with r of order exactly k (or dividing k when nothing better); n = 1: 1."""
    if n == 1: return 1
    best = n
    for r in range(2, n):
        if gcd(r, n) == 1 and pow(r, k, n) == 1:
            o = next(j for j in range(1, k + 1) if pow(r, j, n) == 1)
            if o == k: best = min(best, gcd(r - 1, n))
    return best

def torus_for(fam, q, k):
    """|C_Q(g)| for g of order k in Q/Z (k prime, or 4 meaning an involution of PSL / order-4 element of SL)."""
    p, e = is_pp(q)
    if k == 4:                                        # g^2 = -1 in SL (involution in PSL): C = torus of order q -+ 1 containing it
        if q % 2 == 0: return q                       # conjugation by a unipotent involution: C = U
        return q - 1 if q % 4 == 1 else q + 1         # SL: cyclic of order q -+ 1; PSL: dihedral of order q -+ 1
    if p == k: return 2 * q if (fam == 'sl' and q % 2) else q
    if (q - 1) % k == 0: t = q - 1
    elif (q + 1) % k == 0: t = q + 1
    else: return None
    return t if fam == 'sl' or q % 2 == 0 else t // 2

def mu_A(d, D, N, classes, kA, delta=0.0, g=None):
    """classes: list of (count, |Stab|) for non-generic elements (excluding e). Generic elements have Stab = 1.
    g: group invariants for model.py's first-order coincidence losses (junction swaps, rearrangements mod G')."""
    lam = (W_eff(d, D, N, g) if g is not None else W(d, D)) / N * (1 - delta)
    sides, w = (2, 0.5) if D % 2 else (1, 1.0)
    nonfree = sum(c for c, s in classes)
    tot = (N - 1 - nonfree) * w / kA * math.exp(-lam)
    for c, s in classes: tot += c * (s / kA) * w * math.exp(-lam / s)
    return sides * tot

def options(fam, q, n, d, D):
    """yield (name, kA, classes, delta, layout) for the symmetries available on fam(2,q) x Z_n."""
    p, e = is_pp(q); l = D - 1
    Qord = (q * (q * q - 1)) // (2 if (fam == 'psl' and q % 2) else 1)
    # conjugation of prime order k (orbits of size k)
    for k in (3, 5, 7):
        t = torus_for(fam, q, k)
        if t is None or (d % k > 2 and k > 3): continue   # need f = d mod k <= 2 fixed generators
        fz = fixz(n, k)
        if n > 1 and fz == n: continue
        F = t * fz
        yield ('conj k=%d' % k, k, [(F - 1, k)], 0.0, 'f = %d' % (d % k if d % k <= 2 else 0))
    # Frobenius of order k on GF(p^e), k | e: Fix = fam(2, p^(e/k))
    for k in (2, 3, 5):
        if e % k or (d % k > 2 and k > 3): continue
        q0 = p ** (e // k); fz = fixz(n, k)
        if n > 1 and fz == n: continue
        # Fix = fam(2, q0); for PSL and k = 2 it is PGL(2, q0), which lies in PSL(2, q0^2)
        F = (q0 * (q0 * q0 - 1)) // (2 if (fam == 'psl' and q0 % 2 and k % 2) else 1) * fz
        delta = (1.0 / F + 1.0 / q0 ** 2) * l * l / 8 if k == 2 else 0.0   # k = 2: anti set + sigma-stable tori
        yield ('Frobenius k=%d' % k, k, [(F - 1, k)], delta, 'f = %d' % (d % k if d % k <= 2 else 0))
    # involutive conjugation (k = 2): g^2 central
    t = torus_for(fam, q, 4); fz = fixz(n, 2)
    F = t * fz
    yield ('conj k=2', 2, [(F - 1, 2)], (1.0 / F) * l * l / 8, 'f = %d' % (d % 2))
    # Z_6 = Frobenius (order 2, GF(p^e) over GF(p^(e/2))) x conjugation by g of order 3 in fam(2, p^(e/2))
    if e % 2 == 0:
        q0 = p ** (e // 2)
        t0 = torus_for(fam, q0, 3)                    # C_{Q0}(g), stabiliser = all of Z_6
        if t0 is not None and (n == 1 or fixz(n, 6) < n):
            fz6, fz3, fz2 = fixz(n, 6), fixz(n, 3), fixz(n, 2)
            tQ = (q0 * q0 - 1) if fam == 'sl' or q % 2 == 0 else (q0 * q0 - 1) // 2   # C_Q(g): torus of Q containing g
            Q0 = q0 * (q0 * q0 - 1)                    # Fix(sigma): SL(2,q0), or PGL(2,q0) inside PSL(2,q0^2)
            all6 = t0 * fz6
            stab3 = tQ * fz3 - all6                   # fixed by c_g only
            stab2 = Q0 * fz2 - all6                   # fixed by sigma only
            delta = (1.0 / (Q0 * fz2) + 1.0 / q0 ** 2) * l * l / 8
            yield ('Frob2 x conj3 (Z6)', 6, [(all6 - 1, 6), (stab3, 3), (stab2, 2)], delta, 'f + 2a + 3b + 6c = %d' % d)

def candidate_groups(lo, hi, fams=('sl', 'psl'), nmax=200, qmin=7):
    """Q x Z_n with N in [lo, hi], q >= qmin, n <= min(nmax, q): big cyclic factors mix badly (STRUCTURE §5,
    DATA_CHECK §4e), worse than model.py's rearrangement term says, so they are left out."""
    out = []
    for q in range(qmin, 2100):
        if not is_pp(q): continue
        for fam in fams:
            if fam == 'psl' and q % 2 == 0: continue
            Q = q * (q * q - 1) // (2 if fam == 'psl' else 1)
            if Q > hi: continue
            for n in range(1, min(nmax, q, hi // Q) + 1):
                ps = primes(n)
                if lo <= Q * n <= hi and (all(pp % 3 == 1 for pp in ps) or all(pp % 5 == 1 for pp in ps)):
                    out.append((fam, q, n, Q * n))
    return out

CELLS = {  # cell: (current best N (orbit k=3), table value / 2 or None)
    (7, 8): 47880, (8, 7): 21672, (8, 8): 119952, (9, 8): 255528, (13, 8): 3302208, (7, 9): 231420, (8, 9): 658008,
    (10, 9): 4001928, (11, 9): 8396040, (13, 9): 31936200, (14, 9): 58034328, (16, 9): 162082200, (7, 10): 1117200,
    (8, 10): 3901080, (10, 10): 30070560, (10, 8): 588241, (11, 8): 1123471}

def lam_of(d, D, N): return W(d, D) / N

if __name__ == '__main__':
    print('mu_A and predicted evals (1e5 exp((mu_A - 13)/2)) for groups Q x Z_n with N in [N_best, 1.06 N_best]')
    print('(N_best = current record, or the order that would beat the table for (10,8), (11,8)); SL only at odd D;')
    print('q >= 7, n <= min(200, q), every prime of n = 1 mod 3 or every prime = 1 mod 5; lambda uses model.py W_eff.')
    print('Columns: mu = random-S Poisson mean; then for each symmetry: mu_A (delta = coincidence loss).\n')
    summary = {}
    for (d, D), Nb in sorted(CELLS.items(), key=lambda t: (t[0][1], t[0][0])):
        fams = ('sl',) if D % 2 else ('sl', 'psl')
        gs = candidate_groups(Nb, int(Nb * 1.06), fams)
        rows = []
        for fam, q, n, N in gs:
            mu = N * math.exp(-lam_of(d, D, N))
            g = prod(dict(sl=sl2, psl=psl2)[fam](q), cyc(n)) if n > 1 else dict(sl=sl2, psl=psl2)[fam](q)
            for name, kA, cl, delta, lay in options(fam, q, n, d, D):
                rows.append((mu_A(d, D, N, cl, kA, delta, g), name, fam, q, n, N, mu, delta, cl))
        print('(%d,%d)  N_best = %d, lambda = %.2f, %d candidate groups' % (d, D, Nb, lam_of(d, D, Nb), len(gs)))
        best_by = {}
        for r in sorted(rows):
            if r[1] not in best_by: best_by[r[1]] = r
        for name, r in sorted(best_by.items(), key=lambda t: t[1][0]):
            muA, name, fam, q, n, N, mu, delta, cl = r
            print('   %-20s mu_A %6.1f  (mu %6.1f, delta %.3f)  evals ~ %8.2g   on %s(2,%d) x Z_%d, N = %d, fixed-type counts %s' % (
                name, muA, mu, delta, 1e5 * math.exp(min((muA - 13) / 2, 600)), fam, q, n, N, [c for c, s in cl]))
        summary[(d, D)] = best_by
        print()
    print('summary at the current order: which symmetry type has the lowest mu_A, per cell (count):')
    wins = {}
    for cell, b in summary.items():
        if not b: continue
        w = min(b.values())[1]; wins[w] = wins.get(w, 0) + 1
    print('  ', wins)

    # ---- reach: largest order each symmetry type should solve with a fixed effort ----
    BUDGET = 1e6
    print('\n== reach with <= %.0e evals (effort law), groups with N in [N_best, 1.3 N_best] ==' % BUDGET)
    print('feasible = predicted evals <= budget AND mu_A <= ln(#symmetric S) - 3 (first moment: valid S should exist);')
    print('#S ~ (N/k)^m |Fix|^(f-1) / m!, m = number of free orbits. Gain is over the current best (orbit k = 3) order.')
    print('   cell      current N    ' + '  '.join('%-18s' % t for t in ('conj k=3', 'conj k=5', 'conj k=7', 'Frobenius k=3', 'conj k=2', 'Z6')))
    reach_tab = {}
    for (d, D), Nb in sorted(CELLS.items(), key=lambda t: (t[0][1], t[0][0])):
        fams = ('sl',) if D % 2 else ('sl', 'psl')
        best = {}
        for fam, q, n, N in candidate_groups(Nb, int(Nb * 1.3), fams):
            g = prod(dict(sl=sl2, psl=psl2)[fam](q), cyc(n)) if n > 1 else dict(sl=sl2, psl=psl2)[fam](q)
            for name, kA, cl, delta, lay in options(fam, q, n, d, D):
                muA = mu_A(d, D, N, cl, kA, delta, g)
                kk = 6 if kA == 6 else kA
                f = d % kk if d % kk <= 2 else 0
                m = max((d - f) // kk, 1)
                F = cl[0][0] + 1
                lnS = m * math.log(N / kk) + max(f - 1, 0) * math.log(F) - math.lgamma(m + 1)
                ev = 1e5 * math.exp(min((muA - 13) / 2, 600))
                if ev <= BUDGET and muA <= lnS - 3 and (name not in best or N > best[name][0]):
                    best[name] = (N, fam, q, n, muA)
        key = {'conj k=3': 'conj k=3', 'conj k=5': 'conj k=5', 'conj k=7': 'conj k=7', 'Frobenius k=3': 'Frobenius k=3',
               'conj k=2': 'conj k=2', 'Frob2 x conj3 (Z6)': 'Z6'}
        cells_out = []
        for nm in ('conj k=3', 'conj k=5', 'conj k=7', 'Frobenius k=3', 'conj k=2', 'Frob2 x conj3 (Z6)'):
            if nm in best:
                N, fam, q, n, muA = best[nm]
                cells_out.append('%+5.1f%% %s%d.%d' % (100 * math.log(N / Nb), 'P' if fam == 'psl' else 'S', q, n))
            else: cells_out.append('-')
        reach_tab[(d, D)] = best
        print('   (%2d,%2d)  %11d    ' % (d, D, Nb) + '  '.join('%-18s' % c for c in cells_out))
    print('   (entries: gain in ln N over the current order, and the group: S/P q.n = SL/PSL(2,q) x Z_n)')
