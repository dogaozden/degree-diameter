# Checks behind research/theorems/POLISHED.md (thm-polish, 2026-10-25)

Small independent scripts written for the polished note. Each rebuilds an object from the coordinates printed in
POLISHED.md and checks it. Outputs: `checks.out`, `q4_359.out`.

| script | checks | section |
|---|---|---|
| `thmA.py 3 5 7 9` | AS(q) in the coordinates of §4.1, quadrics 2X0X1 = N and 2eps X0X1 = N: weighted 2-ovoid, copy graph (q+2)-regular of diameter 4 (q = 9 gives the 1782 graph) | §4 |
| `c1w3.py q` (q = 3, 5) | Corollary C1 directly in W(3,q) (cyclic model): clones of C_0 u C_q, two copies of each line of the regular spread; order 2(q^2+1)(q+3), degrees, diameter 4 | §5 |
| `jz.py` | the identities of Lemma 6.6 (a), (b), (d) and Lemma 6.7, symbolically (sympy) | §6 |
| `params.py`, `params9.py` | the table of (c, c0, c1) in §6.3 | §6 |
| `haar_check.py` | the three Haar graphs rebuilt from (G, S) exactly as printed: order and diameter 5 | §8 |
| `q4_359.py` | the (7,4) example: Q(4,5) + one clone per ovoid point + 21 shadow lines with stand-ins (HiGHS optimum), order 359, max degree 7, diameter 4; prints the 21 lines (data in `q4_359_lines.json`) | Appendix A |

`q4_359.py` imports `research/gq4/gq_clones.py` read-only (run with `PYTHONDONTWRITEBYTECODE=1`) and needs scipy.
