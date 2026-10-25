#!/usr/bin/env python3
"""Extra checks for card c8 (run after analyze_z.py): confound and predicted-ratio comparison.
Usage: python3 checks_z.py ZSFILE N
  - confound: Spearman of cost with A on the subset where every z_i is a unit mod n (no z = 0 mod a prime of n)
  - predicted mean/median factor ratios high/low A quartile for exponent e in {7, 9} (e = D-1 for D = 8, 10)
    and lambda in {12.5, 12.9, 17.6}
"""
import math
import sys
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path

import numpy as np

here = Path(__file__).resolve().parent
spec = spec_from_file_location("az", str(here / "analyze_z.py"))
az = module_from_spec(spec)
spec.loader.exec_module(az)

path, n = sys.argv[1], int(sys.argv[2])
rows = az.parse(path)
cost = np.array([c for c, _ in rows], float)
A = np.array([az.A_of(z, n) for _, z in rows])
units = np.array([all(math.gcd(v, n) == 1 for v in z) for _, z in rows])
print("file=%s samples=%d n=%d" % (path, len(rows), n))
print("confound: all z_i units mod n: %d samples, spearman(cost, A) = %.4f (all samples: %.4f)" % (
    units.sum(), az.spearman(cost[units], A[units]), az.spearman(cost, A)))
q1, q3 = np.percentile(A, 25), np.percentile(A, 75)
lo, hi = A <= q1, A >= q3
print("observed: median cost low/high quartile = %.1f / %.1f (ratio %.3f); mean ratio %.3f" % (
    np.median(cost[lo]), np.median(cost[hi]), np.median(cost[hi]) / np.median(cost[lo]), cost[hi].mean() / cost[lo].mean()))
for e in (7, 9):
    for lam in (12.5, 12.9, 17.6):
        f = np.i0(2.0 * lam * A ** e)
        print("predicted e=%d lambda=%.1f: factor ratio high/low mean %.3f, median %.3f" % (
            e, lam, f[hi].mean() / f[lo].mean(), np.median(f[hi]) / np.median(f[lo])))

# collision control: does A add information beyond the number of distinct z-values among the 15?
distinct = np.array([len(set(z)) for _, z in rows], float)
rc, ra, rd = az.rankdata(cost), az.rankdata(A), az.rankdata(distinct)
X = np.column_stack([np.ones_like(rd), rd])
res_c = rc - X @ np.linalg.lstsq(X, rc, rcond=None)[0]
res_a = ra - X @ np.linalg.lstsq(X, ra, rcond=None)[0]
print("collision control: spearman(cost, #distinct z) = %.4f; partial spearman(cost, A | #distinct) = %.4f" % (
    az.spearman(cost, distinct), np.corrcoef(res_c, res_a)[0, 1]))

# exponent fit: least squares of log cost = a + log I0(2 lam A^e) (lam = 12.9), residual sum of squares by e
y = np.log(cost)
fits = []
for e in range(3, 13):
    g = np.log(np.i0(2.0 * 12.9 * A ** e))
    a = np.mean(y - g)
    fits.append((float(np.sum((y - g - a) ** 2)), e))
print("exponent fit RSS by e: " + ", ".join("e=%d:%.1f" % (e, r) for r, e in sorted(fits, key=lambda t: t[1])) +
      "; best e=%d" % min(fits)[1])
