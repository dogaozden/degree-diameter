# Squad round d10D7-r2 (cell (10,7), 2026-10-24): the doubled-matching (DM) sub-problem

**DM construction** (Opus, this session): base = generalized hexagon GH(q) incidence graph + one matching sigma
(point -> line) whose edges are DOUBLED (two parallel edges, voltages 1 and 4 in Z6); hexagon voltages
3*nu with nu in {0,1}. The Z6-lift has 6*|GH(q)| vertices and max degree q+3. At q = 7 that is degree 10 and
**235,296 vertices**, above the (10,7) table value 224,694 = 3*|GH(8)|. Proved (and checked with lift2): every pair of
lift vertices is within distance 7, EXCEPT possibly sheets {0,3} of an *opposite* same-colour pair (v,u) (hexagon
distance 6). Such a pair is fine iff
  (A) the q+1 hexagon geodesics from v to u do not all have the same nu-parity  ("Condition A"), or
  (R) a "route" exists: a walk of length <= 6 from v to u with jump-sum = 0 mod 3 and at least one matching jump.
Facts: routes cover 50.8% of opposite pairs at q = 7 for a random sigma (65.9% at q = 5, 76% at q = 4), and by counting
at most 62.7% at q = 7. A random nu fails (A) on a fraction 2^-q of pairs (q=5: 3.1%, q=7: 0.78%). Pure annealing
of nu with no routes: q=2 floor 72/2016 pairs, q=3 about 7.2%. A sigma tuned to the failures can only cover them if
nu fails (A) on fewer than ~10^5 pairs at q = 7 (about 0.03%, ~25x better than random). So the key question is
**structured nu with Condition-A failure rate far below 2^-q**, plus structured sigma with high route coverage.

Tools (research/d10D7/; do not edit, copy to your folder to modify):
- `dmio.py`: load(q) (points, lines, coordinates over GF(q)), B (polar form), chi (quadratic character),
  write_dm(H, nu, path, sig), score_condA(H, path).
- `dmfast` (source dmfast.c): `NOROUTE=1 ITERS=0 IN=<sol> ./dmfast q` prints "initial cost X (Y%)" = Condition-A
  failures; without NOROUTE it also uses routes of the file's sigma ("with route Z%", cost = pairs failing both);
  ITERS/SECS/TEMP0/TEMP1 anneal nu; SWAPP=p also anneals sigma (slow route recomputation, small q only).
- `lift2` with DM=1 GROUP="cyc 6" J=2 IN=<sol> ITERS=0: exact full check of the lift (cost 0 = DIAMETER_OK).
Costs: q=5 dmfast setup ~2 s (0.25 GB), q=7 ~50 s and 1.6 GB with routes (0.8 GB with NOROUTE).
