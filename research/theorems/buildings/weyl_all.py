"""For each Weyl group (all crystallographic types with |W| <= ~3e6): over ALL w in W compute the graph distance
d_JK(w) of weyl_dist.py and report, for each source class J: the eccentricity (max over w and both target classes),
whether it equals the Coxeter number h, the parity of the far side, and d(w0).  This is the combinatorial core of
Theorem 1 (it is the thin building / Coxeter complex case, and the distance function for every thick building)."""
import sys, time
sys.path.insert(0, '.')
from weyl_dist import analyse, cartan
H = {'A': lambda n: n + 1, 'B': lambda n: 2 * n, 'D': lambda n: 2 * n - 2, 'E': lambda n: {6: 12, 7: 18, 8: 30}[n],
     'F': lambda n: 12, 'G': lambda n: 6}
cases = [('A', n) for n in range(2, 9)] + [('B', n) for n in range(2, 8)] + [('D', n) for n in range(4, 8)] \
        + [('G', 2), ('F', 4), ('E', 6), ('E', 7)]
if len(sys.argv) > 1: cases = [(a[0], int(a[1:])) for a in sys.argv[1:]]
for t, n in cases:
    t0 = time.time()
    C, I, cls, ncls, info, level = analyse(t, n)
    N = max(sum(L) for L in info.values()); h = H[t](n)
    w0 = [lam for lam, L in info.items() if sum(L) == N]; assert len(w0) == 1
    out = []
    for J in (0, 1):
        ecc = 0; far = set()
        for lam in info:
            m = level[J][lam]; Jm = J if m % 2 == 1 else 1 - J
            for K in (0, 1):
                d = m - (1 if Jm == K else 0)
                if d > ecc: ecc, far = d, {K == J}
                elif d == ecc: far.add(K == J)
        m0 = level[J][w0[0]]; Jm0 = J if m0 % 2 == 1 else 1 - J
        d0 = {K: m0 - (1 if Jm0 == K else 0) for K in (0, 1)}
        out.append((ecc, far, d0))
    ok = all(e == h for e, _, _ in out) and all(max(d0.values()) == h for _, _, d0 in out)
    print(f"{t}{n}: |W|={len(info)} N={N} h={h} classes {len(I[0])}+{len(I[1])}; "
          + "; ".join(f"from I{J+1}: ecc {e}, attained at {'same' if far == {True} else 'other' if far == {False} else 'both'} side, "
                      f"d(w0) same/other = {d0[J]}/{d0[1-J]}" for J, (e, far, d0) in enumerate(out))
          + f"  {'OK' if ok else 'FAIL'}  ({time.time()-t0:.0f}s)", flush=True)
