# c8 (wildcard): why the K22 switch is easier than three pairs

Scripts and logs are in this folder: vstats.py (per-new-vertex numbers, with C recovered from sigma by a projective frame),
iso.py (isotropy only), hlines.py (hyperbolic lines against S), k22_fails.txt, k33_fails.txt, c6_fails.txt (anal.py output).

## Per new vertex

misses = opposite-side vertices at base distance >= 5; ball3 = opposite-side vertices within 3; sg4 = same-side pairs at
distance 4 with one walk (single geodesic); niso = switch lines R with C(delta(R)) totally isotropic; fails = failing
(source, target, coset) triples that touch the vertex.

| start (cost) | vertex | misses | ball3 (opp.) | sg4 | switch lines | niso | fails |
|---|---|---|---|---|---|---|---|
| K22 (414) | point x2 | 114, 102 | 473, 485 | 0 | 7, 7 | 7, 7 | 20, 20 |
| K22 (414) | line x2 | 187, 196 | 400, 391 | 0 | 7, 7 | 7, 7 | 94, 116 |
| K33 (648) | point x3 | 154, 159, 151 | 434, 429, 437 | 0 | 6, 6, 6 | 2, 2, 2 | 8, 52, 32 |
| K33 (648) | line x3 | 221, 212, 211 | 367, 376, 377 | 0 | 6, 6, 6 | 2, 3, 1 | 94, 88, 86 |
| C6 in plane (622) | point x3 | 125, 126, 124 | 463, 462, 464 | 0 | 7, 7, 7 | 7, 7, 7 | 18, 24, 24 |
| C6 in plane (622) | line x3 | 189, 198, 191 | 399, 390, 397 | 0 | 7, 7, 7 | 7, 7, 7 | 92, 104, 86 |

Failures by coset over the whole base (top-30 classes of anal.py, so lower bounds): K22 coset 0 = 6 (cosets 1 and 2 = 201
each); K33 coset 0 >= 108 (PP 84, LL 24; cosets 1 and 2 = 254 each); C6 in plane coset 0 = 10 (cosets 1 and 2 about 283).
Same-side single-geodesic pairs (miss.py, ordered counts): K22 278, K33 374. None has a new vertex as an endpoint (sg4 = 0
everywhere), so the single-geodesic difference is on old vertices, not on the new ones.

## Findings

1. Isotropy is the clearest difference. In the K22 start S = {R : C(delta(R)) isotropic} is a plane of PG(3,8) (|S| = 73;
   every hyperbolic line meets S in 1 or 9 points, and 64 hyperbolic lines lie in S). Both K22 switch lines lie in that
   plane, so all 14 stay isotropic. The K33 start has |S| = 65 and keeps 6 of 18. The disjoint K22 variant (r5 c8
   k22c_s11.in, |S| = 81, cost 602) keeps 3 of 14.
2. Non-isotropic switch lines leave old-old distance-4 pairs with a single walk and no sigma-rescue. Coset-0 failures are
   6 for K22 against at least 108 for K33. This is the largest gap in the failure counts.
3. Misses: K33 new points miss 151-159 opposite vertices each (K22: 102-114), and K33 new lines miss 211-221 (K22:
   187-196). Three new neighbours per new vertex give the new part a K_{3,3} (nine 4-cycles) instead of K22's single
   4-cycle, and the 3-balls shrink (points: 429-437 within 3, against 473-485).
4. Isotropy is necessary but not sufficient. The plane K22 from kkk.py PLANE=1 (k22p_test.in, cost 608) is also 14/14
   isotropic, against 414 for the shared-point K22 start. Placement matters as well, so the per-vertex profile does not
   predict the start cost by itself.

## Proposed n = 588 construction: C6 in the plane

Three new points and three new lines with a 6-cycle incidence: each new vertex has 2 new neighbours and 7 switch lines, as in
K22. The switch lines are delta(R) for R on three concurrent hyperbolic lines of the plane S through one point R*, so all
21 switch lines are isotropic. Built with `PLANE=1 PAT="0-0,0-1,1-1,1-2,2-2,2-0" python3 research/d11D5/dc/kkk.py 1 1 c6p.in 6`
(tries 622, 888, 1000, 1070, 1072, 1180; best kept as c6p_start622.in). Its per-vertex numbers follow the K22 pattern
(niso 7/7 at every new vertex; points miss 124-126 against 102-114; lines 189-198 against 187-196; coset-0 count 10 against 6).
Its 3-balls are a little smaller (points 462-464 within 3, against 473-485), which fits the 6-cycle among the new vertices.

## Anneal (one run, po7 T0 1.5 to T1 0.12, SEED 1)

622 -> 152 (c6p_anneal.in, verified with SCORE=1). The run was stopped by the 900 s wall timeout at 372 CPU s, not the
500 s budget, and it was still falling (154 at 366 s, 152 at 372 s). For comparison, K22 went 414 -> 18 in 400 s and the K33
anneals stall near 200. Caveat: after the anneal only 190 of the 582 old points agree with a frame delta o C (the best
frame found by iso.py), so sigma has drifted off the plane structure. The isotropy count printed for the annealed file
(21/21) is therefore not meaningful.

## Scoreboard (n = 588)

Best start 622 (C6 in plane); lowest cost after annealing 152 (not valid). Files: c6p_start622.in, c6p_anneal.in.
