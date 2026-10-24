#!/usr/bin/env python3
"""classes.py: miss rate of each stabiliser class from haar_order2 RANDORB=m CLASSES=1 output (ORDER2.md 5.1).

An element with alpha-orbit of size o has stabiliser H of order h = k/o in <alpha>; the clumped Poisson model says
its words come in groups of h, so it is missed with probability p^(1/h), p = miss rate of free elements (h = 1).
Class k+1 = free elements lying in Anti(alpha^(k/2)): predicted p at even D, ~sqrt(p) at odd D (inversion o beta).
Samples are binned by their own free-element miss rate (quartiles), class rates pooled per bin.
Usage: classes.py FILE.txt [...]   (the header line 'ORBIT k=..' and the D in 'RANDORB d=..' are read from the file)"""
import re, sys, math
import numpy as np

for path in sys.argv[1:]:
    txt = open(path).read()
    k = int(re.search(r"ORBIT k=(\d+)", txt).group(1))
    D = int(re.search(r"d\d+D(\d+)_", path).group(1))       # cell from the file name, e.g. d13D8_...
    m = re.search(r"mu = ([\d.]+)", txt)
    sizes = dict((int(a), int(b)) for a, b in re.findall(r"(\d+):(\d+)", re.search(r"CLASSES sizes[^\n]*\):(.*)", txt).group(1)))
    rows = []
    for ln in re.findall(r"CLASSES sample \d+ cost (\d+) misses(.*)", txt):
        c = int(ln[0]); mm = dict((int(a), int(b)) for a, b in re.findall(r"(\d+):(\d+)", ln[1]))
        rows.append((c, mm))
    sides = 2 if (D and D % 2) else 1
    N = sum(sizes.values())
    rows = [r for r in rows if r[0] < N / 2]      # generating S only
    free = k
    p = np.array([r[1].get(free, 0) / (sides * sizes[free]) for r in rows])
    order = np.argsort(p)
    print(f"== {path}: k={k} D={D} sizes={sizes} generating samples={len(rows)}")
    hdr = "   bin  p(free)    " + "  ".join(f"o={o}(h={k // o if o <= k else 'anti'})" for o in sorted(sizes) if o != free)
    print(hdr)
    for b in range(4):
        idx = order[b * len(order) // 4:(b + 1) * len(order) // 4]
        pb = sum(rows[i][1].get(free, 0) for i in idx) / (sides * sizes[free] * len(idx))
        cells = []
        for o in sorted(sizes):
            if o == free:
                continue
            r = sum(rows[i][1].get(o, 0) for i in idx) / (sides * sizes[o] * len(idx))
            if o <= k:
                h = k // o
                pred = pb ** (1.0 / h) if pb > 0 else float("nan")
                cells.append(f"{r:.4f} (pred {pred:.4f}, ratio {r / pred if pred > 0 else float('nan'):.2f})")
            else:
                pred_even, pred_odd = pb, math.sqrt(pb)
                cells.append(f"{r:.5f} (/p {r / pb if pb > 0 else float('nan'):.2f}, /sqrt p {r / pred_odd if pb > 0 else float('nan'):.2f})")
        print(f"   {b}    {pb:.5f}   " + "   ".join(cells))
