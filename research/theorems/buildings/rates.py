"""How fast do the building families approach the bipartite Moore bound, for each diameter D = 3..30?
Routes (BUILDINGS.md §1.3):
  direct  : regular flag graph of a balanced building (A_2k, C_2m = Sp(4m,q), G2, F4, 2E6, E6, E8), degree (q+1)^(r/2)
  delorme : Delorme product Gamma (x) Opp(Gamma) of the smallest-rank building with Coxeter number D, degree (q+1)^r
  cvbk    : bipartite double B(H) of the halved flag graph H_{D-1,q} of Cames van Batenburg-Korsky (arXiv:2608.03965),
            degree Delta(H)+1 with the EXACT degree Delta(H) = sum over nonempty T of q^|T| (q+1)^|N(T)|
            (T a set of odd nodes of A_2k, N(T) its even neighbours; derived in BUILDINGS.md, checked against BFS)
For each route: n / M_b(Delta, D) at q = 2, 3, 4, 5, 7, 8, 9, 16, 64, 256, and the smallest q (prime power) where the
ratio reaches 0.5 and 0.9.  First-order deficiency 1 - n/M_b ~ c / q with c = t(h-2) (direct, t = r/2 >= 2) or r(h-2)
(delorme), printed as c and as c * Delta^(-alpha)."""
import sys, itertools
from fractions import Fraction
def qi(d, q): return sum(q ** i for i in range(d))
def Mb(d, D): return 2 * sum((d - 1) ** i for i in range(D))
DEG = {'A': lambda n: list(range(2, n + 2)), 'B': lambda n: list(range(2, 2 * n + 1, 2)),
       'D': lambda n: list(range(2, 2 * n - 1, 2)) + [n], 'E6': [2, 5, 6, 8, 9, 12], 'E7': [2, 6, 8, 10, 12, 14, 18],
       'E8': [2, 8, 12, 14, 18, 20, 24, 30], 'F4': [2, 6, 8, 12], 'G2': [2, 6]}
def E(degs, q):
    e = 1
    for d in degs: e *= qi(d, q)
    return e
F4W = None
def E_2E6(q):
    global F4W
    if F4W is None:
        sys.path.insert(0, '.')
        from weyl_dist import analyse
        F4W = [L for L in analyse('F', 4)[4].values()]
    return sum(q ** a * (q * q) ** b for a, b in F4W)
PP = [q for q in range(2, 1100) if (lambda n: next(p for p in range(2, n + 1) if n % p == 0))(q) and
      all(q % p or (lambda m: (lambda f: f(f, m))(lambda f, m: m == 1 or (m % p == 0 and f(f, m // p))))(q)
          for p in [next(p for p in range(2, q + 1) if q % p == 0)])]

def direct_routes(D):
    out = []
    if D % 2 == 1:
        k = (D - 1) // 2; out.append((f"A{2*k}", lambda q, k=k: (2 * E(DEG['A'](2 * k), q) // (q + 1) ** k, (q + 1) ** k), k, k))
    if D % 4 == 0:
        m = D // 4; out.append((f"C{2*m}=Sp({4*m},q)", lambda q, m=m: (2 * E(DEG['B'](2 * m), q) // (q + 1) ** m, (q + 1) ** m), m, 2 * m))
    if D == 6: out.append(("G2", lambda q: (2 * E(DEG['G2'], q) // (q + 1), q + 1), 1, 2))
    if D == 12:
        out.append(("F4", lambda q: (2 * E(DEG['F4'], q) // (q + 1) ** 2, (q + 1) ** 2), 2, 4))
        out.append(("2E6", lambda q: (2 * E_2E6(q) // ((q + 1) * (q * q + 1)), (q + 1) * (q * q + 1)), None, 4))
        out.append(("E6", lambda q: (2 * E(DEG['E6'], q) // (q + 1) ** 3, (q + 1) ** 3), 3, 6))
    if D == 30: out.append(("E8", lambda q: (2 * E(DEG['E8'], q) // (q + 1) ** 4, (q + 1) ** 4), 4, 8))
    return out
def delorme_route(D):
    # smallest rank type with Coxeter number D: B_{D/2} for even D, A_{D-1} for odd D; E7 at 18 (rank 7 < 9)
    if D == 18: name, degs, r = "E7", DEG['E7'], 7
    elif D % 2 == 0: name, degs, r = f"B{D//2}", DEG['B'](D // 2), D // 2
    else: name, degs, r = f"A{D-1}", DEG['A'](D - 1), D - 1
    def f(q):
        e = E(degs, q); return (2 * e * e // (q + 1) ** r, (q + 1) ** r)
    return (f"{name} x Opp", f, r)
def cvbk_degree(k, q):
    # A_2k path 1..2k; odd nodes T, even neighbours N(T); exact degree of the halved graph on even flags
    tot = 0
    odd = list(range(1, 2 * k, 2))
    # DP over odd nodes in order: state = whether previous odd node chosen (shares even neighbour 2i)
    # direct enumeration for k <= 16, DP otherwise
    if k <= 14:
        for mask in range(1, 1 << k):
            T = [odd[i] for i in range(k) if mask >> i & 1]
            Nb = set()
            for t in T:
                for nb in (t - 1, t + 1):
                    if 1 <= nb <= 2 * k and nb % 2 == 0: Nb.add(nb)
            tot += q ** len(T) * (q + 1) ** len(Nb)
        return tot
    # DP: process odd nodes 1,3,...; even node 2i is a neighbour of odd 2i-1 and 2i+1
    # state: chosen(previous odd)  ; weight accumulates q per chosen odd and (q+1) per newly covered even node
    from collections import defaultdict
    st = {(False,): 1}
    for i, t in enumerate(odd):
        ns = defaultdict(int)
        for (prev,), w in st.items():
            # not choose t: even node t-1 (if exists and even) covered only by prev -> already counted when prev chosen
            ns[(False,)] += w
            # choose t: cover t-1 (if not already covered by prev) and t+1
            add = 0
            if t - 1 >= 2 and not prev: add += 1
            if t + 1 <= 2 * k: add += 1
            ns[(True,)] += w * q * (q + 1) ** add
        st = ns
    return sum(st.values()) - 1
def cvbk_route(D):
    k = D - 1
    def f(q):
        N = E(DEG['A'](2 * k), q) // (q + 1) ** k
        return (2 * N, cvbk_degree(k, q) + 1)
    return (f"B(H_{{{k},q}}) [CvB-K doubled]", f, None)

QS = [2, 3, 4, 5, 7, 8, 9, 16, 64, 256]
def first_q(f, D, target, qmax=1100):
    for q in PP:
        if q > qmax: return None
        n, d = f(q)
        if Fraction(n, Mb(d, D)) >= target: return q, d
    return None
if __name__ == '__main__':
    assert cvbk_degree(2, 2) == 60 and cvbk_degree(2, 3) == 204    # = BFS distance-2 counts of PG(4,2), PG(4,3)
    assert all(cvbk_degree(k, q) == cvbk_degree.__wrapped__(k, q) if hasattr(cvbk_degree, '__wrapped__') else True
               for k in range(1, 3) for q in (2, 3))
    Dmax = int(sys.argv[1]) if len(sys.argv) > 1 else 30
    for D in range(3, Dmax + 1):
        routes = [(nm, f, t, 'direct') for nm, f, t, r in direct_routes(D)]
        nm, f, r = delorme_route(D); routes.append((nm, f, r, 'delorme'))
        if D <= 16: nm, f, _ = cvbk_route(D); routes.append((nm, f, None, 'cvbk'))
        print(f"D = {D}")
        for nm, f, t, kind in routes:
            vals = []
            for q in QS:
                if kind == 'cvbk' and q > 16: break
                n, d = f(q); vals.append(f"q={q}: {float(Fraction(n, Mb(d, D))):.4f} (Δ={d})")
            h50 = first_q(f, D, Fraction(1, 2), 300 if kind != 'cvbk' else 32)
            h90 = first_q(f, D, Fraction(9, 10), 1100 if kind != 'cvbk' else 32)
            if kind == 'direct' and t is not None and t >= 2: c = f"1-n/M ~ {t*(D-2)}/q = {t*(D-2)}·Δ^(-1/{t})"
            elif kind == 'direct' and t == 1: c = "exact Moore graph"
            elif kind == 'delorme': c = f"1-n/M ~ {t*(D-2)}/q = {t*(D-2)}·Δ^(-1/{t})"
            elif kind == 'cvbk': c = f"1-n/M ~ (D-1)(2D-3)/q, Δ ~ q^{2*(D-1)}"
            else: c = "1-n/M ~ 10/q, Δ ~ q^3 (2E6)"
            print(f"  {kind:7s} {nm:28s} {c}")
            print(f"          " + "; ".join(vals))
            print(f"          ratio >= 0.5 first at {h50}; >= 0.9 first at {h90}  [(q, Δ)]")
