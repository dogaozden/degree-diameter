# Results: the Sage builders, run in a real Sage

All output below is real: it is what `./run_all.sh` wrote into `logs/` (one minute in total on the cloud machine).

## Environment

* SageMath: **passagemath 10.8.13** (released 2026-10-11), Python 3.13.17, GAP 4.16.1.
* Install route that worked: `python3 -m venv v && v/bin/pip install passagemath-standard` (about 10 minutes, mostly downloading
  wheels). It brings GAP with the small groups library (`passagemath-gap-pkg-smallgrp-data`), which `d5_lift_5_5_384.sage` uses.
  The second pip route and conda-forge were not tried, since the first one worked.
* Run: `SAGE=v/bin/sage ./run_all.sh` from `research/sage/`.

## Summary

(a) = expected vertex count, maximum degree, bipartite and diameter; (b) = comparison with the existing Python builder.

| Family | File | Parameters run | (a) | (b) |
|---|---|---|---|---|
| D=3 four hats | `d3_four_hats.sage` | q = 4, 5 (core and with filler); comparison also q = 7, 8, 9 | all as expected: 2(q²+q+6) vertices, max degree q+2, bipartite, diameter 3; the filled graph is (q+2)-regular | exact edge-set equality with `research/plus2/coords/coords.py` for q = 4, 5, 7, 8, 9 (several (a,c) each, core and filler), also for the three-hat graph |
| D=3 (16,3) | `d3_16_three_gadgets.sage` | PG(2,13), three gadgets | 396 vertices, max degree 16, bipartite, diameter 3 | exact edge-set equality with `research/d3d6/graphs/sym3_q13_d16_n396.json` (2,979 edges) |
| D=4 Theorem A | `d4_theoremA_ASq.sage` | q = 3, 5 (and 7 in the log) | 2q²(q+2) vertices (90, 350, 882), (q+2)-regular, diameter 4; AS(q) is a GQ of order (q−1,q+1); line sums of the weights all 2 | exact equality with `research/gq4x/as_w2.py` for q = 3, 5, 7 |
| D=4 Proposition C | `d4_propC_Wq.sage` | q = 3, 5 (and 7 in the log) | 2(q²+1)(q+3) vertices (120, 416, 1000), (q+3)-regular, diameter 4 | exact equality with `check_d4.py` (`cyclic_W3`, explicit completion) for q = 3, 5 |
| D=4 (7,4) | `d4_7_4_359_Q45.sage` | Q(4,5) | 359 vertices, max degree 7, diameter 4 | exact equality with `check_d4.py`'s construction |
| D=5 (7,5) | `d5_haar_7_5_1200.sage` | SL(2,5) × C5 | 1,200 vertices, 7-regular, diameter 5 | exact equality with the edge list of `research/frontier/build_haar2.py` |
| D=5 (5,5) 360 | `d5_lift_5_5_360.sage` | C15 × S3 | 360 vertices, 5-regular, diameter 5 | exact equality with `build_d5D5_n360_z15s3.py`; isomorphic to the record file `d5D5_n360_lift_g90_6.edges` |
| D=5 (5,5) 384 | `d5_lift_5_5_384.sage` | SmallGroup(96,31) base [[1,4],[4,1]]; SmallGroup(96,17) base [[2,3],[3,2]] | 384 vertices, 5-regular, diameter 5 (both) | exact equality with `d5D5_n384_a1_g96_31.edges` and `d5D5_n384_a2_g96_17.edges`; the Cayley tables from GAP equal the records' tables |
| D=6 Theorem D | `d6_theoremD_hexagon_doubling.sage` | q = 2 (m = 2, 3), q = 3 (m = 2), q = 4 (m = 2, `logs/d6_q4_check.log`); Theorem R for q = 2, 3 | 208, 324, 1,020, 3,524 vertices, max degree q+m, diameter 6; Theorem R: 192, 968 vertices, regular | exact equality with `check_d6.py` (q = 2, 3) and `check_d6_even.py` (q = 4) when the Python whisker set is fed in; at q = 2 the two exact-cover searches pick different whisker sets and the graphs are isomorphic |
| D=7 | `d7_hexagon_copies_hubs.sage` | q = 2 (HHH), q = 3 (HHH, HDH, HDHDH), q = 4 (HDH), small hub graphs | 2NL + hubs vertices, max degree q+1+r, diameter 7 in all five; a control with a random bijection instead of a local duality has diameter 8 | exact equality with `research/synthetic/conics2/typed_build.py` run unchanged on the same inputs, four cases |
| D=8 | `d8_gomez_omegaH.sage` | q = 2 'ab', q = 3 'aba' | as defined (one labelling): diameter **9**, not 8, at q = 2 and q = 3; the audit's per-copy labelling at q = 3 gives diameter **8** | exact equality with `check_d8.py`'s builder (thesis labelling q = 2, 3; the repaired q = 3 graph after relabelling by an isomorphism) |

## What these runs do not show

* **D=7.** These are small instances of the general builder (q = 2, 3, 4, a few hubs). They check Theorems 4.3, 4.5 and 4.6 at those
  sizes; they are not the records. The records ((7,7), (9,7), … with 10⁶ to 10⁸ vertices) are not built. The `typed_build.py`
  comparison used the same freed sets, local duality σ and hub graph as the Sage run; the Sage file computes those itself
  (`friendly_sets`, `sigma_local_duality`) and the comparison feeds the same R′ and hub graph to `typed_build.py`.
* **D=8.** The construction as defined has diameter 9 (SYNTHETIC.md Theorem 6.2); the runs confirm it for q = 2 and q = 3. The
  per-copy labelling that gives diameter 8 at q = 3 is the lab's table-audit file, copied into `data/`; we have no description of it.
  The repo has no repaired labelling at q = 2, so that case (SYNTHETIC.md §6.3) is not reproduced here.
* **D=3 (16,3).** The record is the three gadgets plus three edges Q_{g+1} ~ M_g. The gadgets alone have diameter 4 (printed in the log).
  The frames are given as Singer exponents; they were found by the lab's search and are not derived.
* **D=4 Proposition C.** The completion step depends on a numbering of the spread lines; the Sage file numbers them by the Singer
  index i, and the comparison passes the Python numbering to the Sage function, so the exact equality is for that numbering.
* **D=6.** q = 5 and above are impractical for `hexagon.sage` (estimated, not run); q = 4 takes about 6 seconds for the hexagon alone.
  The q = 4 doubling is run by `sage -c` (`logs/d6_q4_check.log`) and compared in `compare_d6`.

## Full output

### D = 3 · four hats (`d3_four_hats.sage`) and the (16,3) record (`d3_16_three_gadgets.sage`)

`logs/d3_check.log`
```
four hats, q=4, core: vertices 52 (expected 52), max degree 6 (expected 6), bipartite True, diameter 3 (expected 3)  ->  OK
four hats, q=4, with filler: vertices 52 (expected 52), max degree 6 (expected 6), bipartite True, diameter 3 (expected 3)  ->  OK
   filled graph is 6-regular: True
four hats, q=5, core: vertices 72 (expected 72), max degree 7 (expected 7), bipartite True, diameter 3 (expected 3)  ->  OK
four hats, q=5, with filler: vertices 72 (expected 72), max degree 7 (expected 7), bipartite True, diameter 3 (expected 3)  ->  OK
   filled graph is 7-regular: True
```

`logs/d3_16_check.log`
```
degrees: [14, 15, 16]  edges: 2979
(16,3), PG(2,13) + three four-hat gadgets + 3 cross edges: vertices 396 (expected 396), max degree 16 (expected 16), bipartite True, diameter 3 (expected 3)  ->  OK
without the 3 cross edges: edges 2976  diameter 4 (the cross edges are needed)
```

Comparison with the lab's Python builder (`compare/compare_d3.sage`, `logs/compare_d3.log`):
```
four hats vs coords.py
  four hats q=4 a=2 c=3 filler=False: edges 153 vs 153, exact edge-set equality: True
  four hats q=4 a=2 c=3 filler=True: edges 156 vs 156, exact edge-set equality: True
  four hats q=4 a=3 c=2 filler=False: edges 153 vs 153, exact edge-set equality: True
  four hats q=4 a=3 c=2 filler=True: edges 156 vs 156, exact edge-set equality: True
  four hats q=5 a=2 c=3 filler=False: edges 244 vs 244, exact edge-set equality: True
  four hats q=5 a=2 c=3 filler=True: edges 252 vs 252, exact edge-set equality: True
  four hats q=5 a=2 c=4 filler=False: edges 244 vs 244, exact edge-set equality: True
  four hats q=5 a=2 c=4 filler=True: edges 252 vs 252, exact edge-set equality: True
  four hats q=5 a=3 c=2 filler=False: edges 244 vs 244, exact edge-set equality: True
  four hats q=5 a=3 c=2 filler=True: edges 252 vs 252, exact edge-set equality: True
  four hats q=5 a=3 c=4 filler=False: edges 244 vs 244, exact edge-set equality: True
  four hats q=5 a=3 c=4 filler=True: edges 252 vs 252, exact edge-set equality: True
  four hats q=5 a=4 c=2 filler=False: edges 244 vs 244, exact edge-set equality: True
  four hats q=5 a=4 c=2 filler=True: edges 252 vs 252, exact edge-set equality: True
  four hats q=5 a=4 c=3 filler=False: edges 244 vs 244, exact edge-set equality: True
  four hats q=5 a=4 c=3 filler=True: edges 252 vs 252, exact edge-set equality: True
  four hats q=7 a=2 c=3 filler=False: edges 534 vs 534, exact edge-set equality: True
  four hats q=7 a=2 c=3 filler=True: edges 558 vs 558, exact edge-set equality: True
  four hats q=7 a=5 c=4 filler=False: edges 534 vs 534, exact edge-set equality: True
  four hats q=7 a=5 c=4 filler=True: edges 558 vs 558, exact edge-set equality: True
  four hats q=8 a=2 c=3 filler=False: edges 745 vs 745, exact edge-set equality: True
  four hats q=8 a=2 c=3 filler=True: edges 780 vs 780, exact edge-set equality: True
  four hats q=8 a=7 c=5 filler=False: edges 745 vs 745, exact edge-set equality: True
  four hats q=8 a=7 c=5 filler=True: edges 780 vs 780, exact edge-set equality: True
  four hats q=9 a=2 c=3 filler=False: edges 1008 vs 1008, exact edge-set equality: True
  four hats q=9 a=2 c=3 filler=True: edges 1056 vs 1056, exact edge-set equality: True
  four hats q=9 a=8 c=4 filler=False: edges 1008 vs 1008, exact edge-set equality: True
  four hats q=9 a=8 c=4 filler=True: edges 1056 vs 1056, exact edge-set equality: True
three hats (Araujo-Pardo--Lopez) vs coords.py
  three hats q=4 a=2: edges 144 vs 144, exact edge-set equality: True
  three hats q=4 a=3: edges 144 vs 144, exact edge-set equality: True
  three hats q=5 a=2: edges 233 vs 233, exact edge-set equality: True
  three hats q=5 a=3: edges 233 vs 233, exact edge-set equality: True
  three hats q=5 a=4: edges 233 vs 233, exact edge-set equality: True
  three hats q=9 a=2: edges 989 vs 989, exact edge-set equality: True
  three hats q=9 a=5: edges 989 vs 989, exact edge-set equality: True
(16,3) vs the verified record file
  (16,3): Sage 396 vertices 2979 edges, json 396 vertices 2979 edges, exact edge-set equality with sym3_q13_d16_n396.json: True
ALL COMPARISONS PASS
```

### D = 4 · Theorem A, Proposition C, the (7,4) example

(The q = 7 runs are in `logs/d4_q7_check.log`.)

`logs/d4_theoremA_check.log`
```
AS(3) is a generalized quadrangle of order (2,4): True
weighted 2-ovoid (eps=2, c1=1, c2=2): total weight 18, line sums {2}
Theorem A, q=3: vertices 90 (expected 90), max degree 5 (expected 5), bipartite True, diameter 4 (expected 4)  ->  OK
   (q+2)-regular: True
AS(5) is a generalized quadrangle of order (4,6): True
weighted 2-ovoid (eps=2, c1=1, c2=2): total weight 50, line sums {2}
Theorem A, q=5: vertices 350 (expected 350), max degree 7 (expected 7), bipartite True, diameter 4 (expected 4)  ->  OK
   (q+2)-regular: True
```

`logs/d4_propC_check.log`
```
W(3): 40 points, 40 lines; O has 20 points and meets every line twice: True; the 10 spread lines partition the points: True
core (before the completion): degrees [4, 6]
Proposition C, q=3: vertices 120 (expected 120), max degree 6 (expected 6), bipartite True, diameter 4 (expected 4)  ->  OK
   (q+3)-regular: True
W(5): 156 points, 156 lines; O has 52 points and meets every line twice: True; the 26 spread lines partition the points: True
core (before the completion): degrees [6, 8]
Proposition C, q=5: vertices 416 (expected 416), max degree 8 (expected 8), bipartite True, diameter 4 (expected 4)  ->  OK
   (q+3)-regular: True
```

`logs/d4_7_4_check.log`
```
Q(4,5): 156 points, 156 lines, ovoid of 26 points meeting every line once: True
(7,4): Q(4,5) + 26 clones + 21 shadow lines: vertices 359 (expected 359), max degree 7 (expected 7), bipartite True, diameter 4 (expected 4)  ->  OK
```

Comparison with the lab's Python builder (`compare/compare_d4.sage`, `logs/compare_d4.log`):
```
Theorem A vs research/gq4x/as_w2.py
  Theorem A q=3: Sage 90 vertices 225 edges, Python 225 edges, exact edge-set equality: True
  Theorem A q=5: Sage 350 vertices 1225 edges, Python 1225 edges, exact edge-set equality: True
  Theorem A q=7: Sage 882 vertices 3969 edges, Python 3969 edges, exact edge-set equality: True
Proposition C vs research/synthetic/checks/check_d4.py
  Proposition C q=3: Sage 120 vertices 360 edges, Python 360 edges, exact edge-set equality: True
  Proposition C q=5: Sage 416 vertices 1664 edges, Python 1664 edges, exact edge-set equality: True
(7,4) example vs research/synthetic/checks/check_d4.py
  (7,4): Sage 359 vertices 1218 edges, Python 1218 edges, exact edge-set equality: True
ALL COMPARISONS PASS
```

### D = 5 · the (7,5) Haar graph, the (5,5) lifts on 360 and 384 vertices

`logs/d5_haar_check.log`
```
(7,5): Haar graph of SL(2,5) x Z_5, |S| = 7: vertices 1200 (expected 1200), max degree 7 (expected 7), bipartite True, diameter 5 (expected 5), regular  ->  OK
```

`logs/d5_lift360_check.log`
```
(5,5): lift of [[2,3],[3,2]] by C15 x S3: vertices 360 (expected 360), max degree 5 (expected 5), bipartite True, diameter 5 (expected 5), regular  ->  OK
```

`logs/d5_lift384_check.log`
```
SmallGroup(96,31) = C3 : (C2 . ((C4 x C2) : C2) = (C2 x C2) . (C4 x C2)): Cayley table equals the record table g96_31.txt: True
(5,5): lift by SmallGroup(96,31), a1_g96_31: vertices 384 (expected 384), max degree 5 (expected 5), bipartite True, diameter 5 (expected 5), regular  ->  OK
SmallGroup(96,17) = C3 : (Q8 : C4): Cayley table equals the record table g96_17.txt: True
(5,5): lift by SmallGroup(96,17), a2_g96_17: vertices 384 (expected 384), max degree 5 (expected 5), bipartite True, diameter 5 (expected 5), regular  ->  OK
```

Comparison with the lab's Python builder (`compare/compare_d5.sage`, `logs/compare_d5.log`):
```
  (7,5) 1200: build_haar2.py edge list (1200 vertices, 4200 edges) vs Sage (1200 vertices, 4200 edges): exact edge-set equality True
  (5,5) 360: build_d5D5_n360_z15s3.py edge list (360 vertices, 900 edges) vs Sage: exact edge-set equality True
  (5,5) 360: record file d5D5_n360_lift_g90_6.edges (360 vertices, 900 edges): isomorphic to the Sage graph: True
  (5,5) 384 a1_g96_31: record file d5D5_n384_a1_g96_31.edges (384 vertices, 960 edges) vs Sage (384 vertices, 960 edges): exact edge-set equality True
  (5,5) 384 a2_g96_17: record file d5D5_n384_a2_g96_17.edges (384 vertices, 960 edges) vs Sage (384 vertices, 960 edges): exact edge-set equality True
ALL COMPARISONS PASS
```

### D = 6 · Theorem D and Theorem R

`logs/d6_check.log`
```
H(2): N = 63, |Sigma| = 9, free points 24, |W| = 12, c = 1
Theorem D, q=2, m=2: vertices 208 (expected 208), max degree 4 (expected 4), bipartite True, diameter 6 (expected 6)  ->  OK
   block-by-block edges equal the generic definition 3.1: True
Theorem R, q=2, m=2: vertices 192 (expected 192), max degree 4 (expected 4), bipartite True, diameter 6 (expected 6), min degree 4  ->  OK
H(2): N = 63, |Sigma| = 9, free points 24, |W| = 12, c = 1
Theorem D, q=2, m=3: vertices 324 (expected 324), max degree 5 (expected 5), bipartite True, diameter 6 (expected 6)  ->  OK
   block-by-block edges equal the generic definition 3.1: True
H(3): N = 364, |Sigma| = 28, free points 216, |W| = 72, c = 1
Theorem D, q=3, m=2: vertices 1020 (expected 1020), max degree 5 (expected 5), bipartite True, diameter 6 (expected 6)  ->  OK
   block-by-block edges equal the generic definition 3.1: True
Theorem R, q=3, m=2: vertices 968 (expected 968), max degree 5 (expected 5), bipartite True, diameter 6 (expected 6), min degree 5  ->  OK
```

Comparison with the lab's Python builder (`compare/compare_d6.sage`, `logs/compare_d6.log`):
```
[q=3] (a) hexagon flag sets equal after relabelling: True
[q=3] (b) Hermitian spread equal: True   (Sage c = 1)
[q=3] (c) whisker sets: Sage default = Python  (|W| = 72)
[q=3] (d) Sage doubling with the Python whiskers: 1020 vertices; edge set EXACTLY equal to the Python one: True
[q=2] (a) hexagon flag sets equal after relabelling: True
[q=2] (b) Hermitian spread equal: True   (Sage c = 1)
[q=2] (c) whisker sets: Sage default != Python  (|W| = 12)
[q=2] (d) Sage doubling with the Python whiskers: 208 vertices; edge set EXACTLY equal to the Python one: True
[q=2]     Sage default whiskers: graph has 208 vertices, degrees [3, 4]; is_isomorphic to the Python graph: True
check_d6_even.py output: H(4): 1365 points; (c0,c1) = (2,0); |W| = 240; doubled: 3524 elements, max degree 6 | ALL CHECKS PASSED
[q=4] (a) hexagon flag sets equal after relabelling: True
[q=4] (b) Hermitian spread equal: True   (Sage c = t)
[q=4] (c) whisker sets: Sage default = Python  (|W| = 240)
[q=4] (d) Sage doubling with the Python whiskers: 3524 vertices; edge set EXACTLY equal to the Python one: True
ALL COMPARISONS EQUAL [('q=3', True), ('q=2', True), ('q=4', True)]
```

### D = 7 · copies of a hexagon with freed sets and hubs

`logs/d7_check.log`
```
q=2 types HHH, r=1, 1+1 hubs on a 2-cycle: vertices 380 (expected 380), max degree 4 (expected 4), bipartite True, diameter 7 (expected 7)  ->  OK
q=3 types HHH, r=1, 3+3 hubs on a 6-cycle: vertices 2190 (expected 2190), max degree 5 (expected 5), bipartite True, diameter 7 (expected 7)  ->  OK
q=3 types HDH, r=1, 3+3 hubs on a 6-cycle: vertices 2190 (expected 2190), max degree 5 (expected 5), bipartite True, diameter 7 (expected 7)  ->  OK
q=3 types HDHDH, r=2, 1+1 hubs on a 2-cycle: vertices 3642 (expected 3642), max degree 6 (expected 6), bipartite True, diameter 7 (expected 7)  ->  OK
q=4 types HDH, r=1, 3+3 hubs on a 6-cycle: vertices 8196 (expected 8196), max degree 6 (expected 6), bipartite True, diameter 7 (expected 7)  ->  OK
control (q=3, HHH, random bijection instead of a local duality): 2190 vertices, diameter 8 (> 7 expected)  ->  OK
```

Comparison with the lab's Python builder (`compare/compare_d7.sage`, `logs/compare_d7.log`):
```
q=3 HHH K=3: typed_build.py 2190 vertices 5475 edges; Sage 2190 vertices 5475 edges; EXACT equal after relabelling: True
q=3 HDH K=3: typed_build.py 2190 vertices 5285 edges; Sage 2190 vertices 5285 edges; EXACT equal after relabelling: True
q=3 HDHDH K=1: typed_build.py 3642 vertices 10339 edges; Sage 3642 vertices 10339 edges; EXACT equal after relabelling: True
q=4 HDH K=3: typed_build.py 8196 vertices 24006 edges; Sage 8196 vertices 24006 edges; EXACT equal after relabelling: True
compare_d7: ALL EQUAL
```

### D = 8 · Gómez's construction with per-copy labellings

`logs/d8_check.log`
```
q=2 ab, thesis labelling, reading 2 (as defined: diameter >= 9): vertices 1890 (expected 1890), max degree 5 (expected 5), bipartite True, diameter 9 (expected 9)  ->  OK
q=3 aba, thesis labelling, reading 2 (as defined: diameter >= 9): vertices 14560 (expected 14560), max degree 6 (expected 6), bipartite True, diameter 9 (expected 9)  ->  OK
q=3 aba, audit labelling (per-copy), reading 1 (repair): vertices 14560 (expected 14560), max degree 6 (expected 6), bipartite True, diameter 8 (expected 8)  ->  OK
```

Comparison with the lab's Python builder (`compare/compare_d8.sage`, `logs/compare_d8.log`):
```
q=2 ab thesis labelling: Python 4410 edges, Sage 4410 edges; EXACT equal after relabelling: True
q=3 aba thesis labelling: Python 43680 edges, Sage 43680 edges; EXACT equal after relabelling: True
q=3 repaired (audit labelling): Python 43680 edges, Sage 43680 edges; EXACT equal after relabelling by the isomorphism audit base -> H(3): True
compare_d8: ALL EQUAL
```

### Extra runs

`logs/d4_q7_check.log` (Theorem A and Proposition C at q = 7):
```
AS(7) is a generalized quadrangle of order (6,8): True
weighted 2-ovoid (eps=3, c1=1, c2=3): total weight 98, line sums {2}
Theorem A, q=7: vertices 882 (expected 882), max degree 9 (expected 9), bipartite True, diameter 4 (expected 4)  ->  OK
   (q+2)-regular: True
W(7): 400 points, 400 lines; O has 100 points and meets every line twice: True; the 50 spread lines partition the points: True
core (before the completion): degrees [8, 10]
Proposition C, q=7: vertices 1000 (expected 1000), max degree 10 (expected 10), bipartite True, diameter 4 (expected 4)  ->  OK
   (q+3)-regular: True
```

`logs/d6_q4_check.log` (Theorem D at q = 4):
```
H(4): N = 1365, |Sigma| = 65, free points 960, |W| = 240, c = t
Theorem D, q=4, m=2: vertices 3524 (expected 3524), max degree 6 (expected 6), bipartite True, diameter 6 (expected 6)  ->  OK
   block-by-block edges equal the generic definition 3.1: True
```

`logs/hexagon_selftest.log` (the hexagon helper):
```
H(2): 126 vertices (2N = 126), degrees [3], bipartite True, diameter 6, girth 12; Hermitian spread: 9 lines (q^3+1 = 9) -> OK
H(3): 728 vertices (2N = 728), degrees [4], bipartite True, diameter 6, girth 12; Hermitian spread: 28 lines (q^3+1 = 28) -> OK
```
