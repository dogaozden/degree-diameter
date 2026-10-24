"""General (non-bipartite) graphs, for comparison (BUILDINGS.md §1.7(f)).  Ratio |G| / M(Delta, D), M = general
Moore bound 1 + Delta sum_{i<D} (Delta-1)^i, at several q, for:
  cvbk     : halved flag graph H_{D,q} of Cames van Batenburg-Korsky, exact degree (rates.cvbk_degree)
  isham    : polarity quotient P(C(k,q)) of Isham et al. (D = 2k even), degree (q+1)^k
  delormeA : Delorme quotient of the A_D(q) flag graph: order |A||B| = E^2/(q+1)^D, degree <= (q+1)^D, diameter <= D
  delormeB : Delorme quotient of the B_{(D+1)/2}(q) flag graph (D odd): degree <= (q+1)^((D+1)/2), diameter <= D
The ratio uses the degree bound (q+1)^r for the Delorme quotients (the true max degree is the same, loops only lower
some degrees by 1)."""
import sys
sys.path.insert(0, '.')
from rates import cvbk_degree, E, DEG
def M(d, D): return 1 + d * sum((d - 1) ** i for i in range(D))
QS = [2, 3, 4, 5, 7, 8, 9, 16, 64, 256]
for D in range(2, 13):
    print(f"D = {D}")
    rows = []
    rows.append(("cvbk H_{D,q}", lambda q: (E(DEG['A'](2 * D), q) // (q + 1) ** D, cvbk_degree(D, q)), 16))
    if D % 2 == 0:
        k = D // 2
        rows.append((f"isham P(C({k},q))", lambda q, k=k: (E(DEG['A'](2 * k), q) // (q + 1) ** k, (q + 1) ** k), 256))
    rows.append((f"delorme A{D} quotient", lambda q: (E(DEG['A'](D), q) ** 2 // (q + 1) ** D, (q + 1) ** D), 256))
    if D % 2 == 1:
        r = (D + 1) // 2
        rows.append((f"delorme B{r} quotient", lambda q, r=r: (E(DEG['B'](r), q) ** 2 // (q + 1) ** r, (q + 1) ** r), 256))
    for nm, f, qmax in rows:
        vals = []
        for q in QS:
            if q > qmax: break
            n, d = f(q); vals.append(f"q={q}: {n / M(d, D):.4f} (Δ={d})")
        print(f"  {nm:24s} " + "; ".join(vals))
