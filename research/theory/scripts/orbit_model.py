"""The clumped Poisson model of BEYOND_RANDOM.md §1 for alpha-invariant S, and the group data it needs.

For a group A of automorphisms with alpha(S) = S (plus, for odd D, the inversion that already pairs x with x^-1), the
uncovered set is A-invariant. The expected number of uncovered A-orbits ("clumps") is

    mu_A = sides * sum_x (|Stab_A(x)| / |A|) * exp(-lambda_x / |Stab_A(x)|),

where lambda_x is the random-S Poisson rate of words hitting x. For random S (A = 1, or A = <inversion> at odd D) this
is model.py's mu. Here A = <alpha> of prime order k (times inversion for odd D). Every class of targets in model.py
splits into its alpha-free part (weight / k, same rate) and its alpha-fixed part (same weight, rate / k)."""
import math
from math import gcd
from model import W, W_eff, Wlen
from groups_inv import sl2, psl2, pgl2, cyc, prod

# ---------- group parsing (RESULT 'group=' strings and sols headers) ----------
def parse_group(spec):
    """'psl 19 x Z_14', 'sl 8 poly x^3+x+1 x Z_43', 'prod sl 8 poly .. sl 8 poly .. x Z_13' -> list of (fam, q), n."""
    t = spec.split()
    n = int(t[t.index('x', len(t) - 2) + 1][2:]) if t[-1].startswith('Z_') else 1
    t = t[:-2] if t[-1].startswith('Z_') else t
    if t[0] == 'prod': t = t[1:]
    Qs, i = [], 0
    while i < len(t):
        fam, q = t[i], int(t[i + 1]); i += 2
        if i < len(t) and t[i] == 'poly': i += 2
        Qs.append((fam, q))
    return Qs, n

def qinv(fam, q):
    return dict(sl=sl2, psl=psl2, pgl=pgl2)[fam](q)

def group_invariants(Qs, n):
    g = prod(*[qinv(f, q) for f, q in Qs], cyc(n)) if n > 1 else (prod(*[qinv(f, q) for f, q in Qs]) if len(Qs) > 1 else qinv(*Qs[0]))
    return g

def centralizer_order3(fam, q):
    """(|C_Q(g)|, #involutions in C_Q(g), |Z(Q)|) for g whose conjugation has order 3 (g of order 3 in Q/Z(Q))."""
    p = min(f for f in range(2, q + 1) if q % f == 0)
    if p == 3:                                   # unipotent: C = Z(Q) x U, U elementary abelian of order q
        if fam == 'sl': return 2 * q, 1, 2
        return q, 0, 1                           # psl (pgl has C = U too: q)
    t = q - 1 if q % 3 == 1 else q + 1           # the torus containing elements of order 3
    if fam == 'sl': return t, (1 if q % 2 else 0), (2 if q % 2 else 1)
    if fam == 'psl':
        if q % 2 == 0: return t, 0, 1
        return t // 2, (1 if (t // 2) % 2 == 0 else 0), 1
    if fam == 'pgl': return t, (1 if t % 2 == 0 else 0), 1
    raise ValueError(fam)

def best_r(n, k=3):
    """haar_sym's choice: r with r^k = 1 mod n, gcd(r, n) = 1, fewest fixed z (gcd(r-1, n)); 1 if none."""
    best, bf = 1, n
    for r in range(2, n):
        if gcd(r, n) == 1 and pow(r, k, n) == 1 % n:
            fx = gcd(r - 1, n)
            if fx < bf: best, bf = r, fx
    return best

def alpha_data(Qs, n, k=3):
    """Fixed-point structure of alpha = (conjugation by an order-3 element on every Q factor) x (z -> r z)."""
    C, Ci, ZQ = 1, 1, 1
    for f, q in Qs:
        c, ci, z = centralizer_order3(f, q); C *= c; Ci *= (ci + 1); ZQ *= z   # Ci: #{x in C: x^2 = e}
    r = best_r(n, k) if n > 1 else 1
    fz = [z for z in range(n) if ((r - 1) * z) % n == 0]
    fz_sq = sum(1 for z in fz if (2 * z) % n == 0)                             # incl. 0
    ZQsq = ZQ                                                                  # Z(Q) = {+-1}^j: all square to e
    fix = C * len(fz)                                                          # incl. e
    fix_sq = Ci * fz_sq                                                        # x^2 = e, incl. e
    fix_c = ZQ * len(fz)                                                       # central and fixed, incl. e
    fix_c_sq = ZQsq * fz_sq
    return dict(k=k, r=r, fix=fix, fix_inv=fix_sq - 1, fix_c=fix_c - 1, fix_c_inv=fix_c_sq - 1)

# ---------- the clumped Poisson mean ----------
def classes(d, D, N, g, coincid=True):
    """model.py's target classes as (count, weight, rate) per side, plus the number of sides.
    count: elements; weight: 1/clump size under inversion; rate: Poisson rate of words hitting one element."""
    we = W_eff(d, D, N, g, coincid) if g is not None else float(W(d, D)); lam = we / N
    if D % 2 == 0:
        return 1, dict(generic=(N - 1, 1.0, lam))
    k2 = (D - 1) // 2; scale = we / W(d, D)
    rot = scale * sum(Wlen(d, 2 * j) / j for j in range(1, k2 + 1)) / N
    Z, I, Ic = g['Z'], g['inv'], g['inv_c']; Inc = I - Ic
    return 2, dict(generic=(N - Z - Inc, 0.5, lam), involutions=(Inc, 1.0, lam / 2),
                   central=(Z - 1 - Ic, 0.5, rot), central_inv=(Ic, 1.0, rot / 2))

def mu_rand(d, D, N, g, coincid=True):
    sides, cl = classes(d, D, N, g, coincid)
    return sides * sum(c * w * math.exp(-r) for c, w, r in cl.values())

def mu_orbit(d, D, N, g, a, coincid=True, parts=False):
    """clumped mean for alpha-invariant S. a = alpha_data(...) (fixed counts exclude e, which is always covered)."""
    k = a['k']; sides, cl = classes(d, D, N, g, coincid)
    if D % 2 == 0:
        fixed = {'generic': a['fix'] - 1}
    else:
        fixed = dict(generic=a['fix'] - 1 - a['fix_inv'] - (a['fix_c'] - a['fix_c_inv']),
                     involutions=a['fix_inv'] - a['fix_c_inv'], central=a['fix_c'] - a['fix_c_inv'], central_inv=a['fix_c_inv'])
    out = {}
    for name, (c, w, r) in cl.items():
        cf = fixed.get(name, 0)
        out[name + '_free'] = sides * (c - cf) * w / k * math.exp(-r)
        out[name + '_fixed'] = sides * cf * w * math.exp(-r / k)
    return (sum(out.values()), out) if parts else sum(out.values())

def lam(d, D, N): return W(d, D) / N
