# c5 notes: order-3 automorphisms with fixed vertices

Start: 2026-10-31T15:44:35Z (date -u). Stop about 17:44Z.

Card: order-3 automorphism s of a cubic bipartite graph G (n = 2m). s preserves both sides (odd order).
Fixed vertices are pairwise non-adjacent and each fixed vertex has its 3 neighbours in one regular orbit of the
other side. Encoding: regular orbits have 3 copies, fixed vertices are singletons. Quotient edges (ao, bo, t)
join (ao,i) to (bo,i+t); fixed A-vertex k attaches to a whole B-orbit; fixed B-vertex attaches to an A-orbit.
Slots: each regular orbit has 3 slots; fixed attachments use one slot.
Cost = far (unordered pairs at distance > 7), computed by bit-parallel BFS from one representative per orbit,
weighted by orbit size (3 regular, 1 fixed).

## Results so far (16:45Z)

Tools (all in c5/): `fixsa.c` (quotient SA / full-neighbourhood tabu / ILS; env INIT=state file, INIT_EVERY, TABU=secs,
ILS=secs, PFOCUS=p, EVAL=1 prints cost of INIT), `py/auts.py` (all 504 automorphisms of conder168 by backtracking with
distance pruning, output out/aut168.txt), `py/quot.py` (graph + automorphism of order 3 -> quotient state file),
`py/surgery.py` (n -> n+2 surgery: delete one quotient edge, attach a fixed A vertex to its B-orbit and a fixed B vertex to
its A-orbit), `py/dsurgery.py` (double surgery), `py/eval_all.sh`, `py/farstat.py`.
Cost check: fixsa's cost equals score37's far on every graph checked (132, 80, 150, 105, 120 agree).

Structure of conder168 (from auts.py): |Aut| = 504. Order-3 elements: 22 fixed-point-free (3^56), i.e. 11 free Z3
subgroups; 112 elements with 3 fixed vertices (1^3 3^55), i.e. 56 subgroups, the 3 fixed vertices all on ONE side
(FA = 3, FB = 0). Quotient states: out/states/c168free.state (AR=BR=28, E=84) and c168fix.state (FA=3, AR=27, BR=28,
E=81). Both evaluate to cost 0 in fixsa (calibration: the representation is right).

Calibration of plain SA (fixsa from random starts, 40-60 s, T 3 -> 0.5 or 10 -> 1):
- n=150, free Z3 (FA=FB=0): best far 12.
- n=168 free Z3: best 105-129 (60 s).  n=168 with FA=FB=3 : 105 (60 s).   (the known quotient has cost 0)
- n=168 free, one 150M-move run split in 3 x 20M: 150 (T 2 -> 0.2 is too cold: stuck after 30k moves).
- n=170, FA=4 FB=1 random start, 170 s: best 137. FA=1 FB=1 random 20 s: 132.
Conclusion: plain quotient SA cannot even find the known 168 solution; the random-start ceiling is about 120-135 at n = 168-170.

Surgery from conder168 (exhaustive over all deletions, costs from EVAL):
- free quotient (FA=FB=0) -> n=170 (FA=FB=1): 84 surgeries, best 129 (24 of them 129).
- 3-fixed quotient -> n=170 (FA=4, FB=1): 81 surgeries, best 92 (three of them), distribution 92,93,95,103,126,132,...
- Repair (SA at T 3-4 -> 0.5, 30-60 s from the best surgeries, 7 of them): every run from a 92-start ends at exactly
  far = 80. The free-quotient starts end at 105. Random-start SA gives 137 in 170 s.
- Best n=170 in this family: far 80, file c5/best170_far80.edges (a correction row is in scoreboard.tsv: c1 already has
  46 at n=170, so this is NOT an improvement and was not logged as one).
- Far pairs of the far-80 graph: 41 same-side pairs in A, 39 in B, none across sides. Per-vertex counts are 0..5; the
  4 fixed A vertices have far counts 1, 1, 0, 5 and the fixed B vertex 0.
- Double surgery (free quotient -> n=172, FA=FB=2): 3486 choices, best 247 (EVAL), useless.
- Single surgery from the far-80 state to n=172 (FA=5, FB=2): best surgery 169, repaired only to 161. Chaining
  surgeries from already-repaired states does not work.

Tabu / ILS (from the far-80 state at n=170):
- full-neighbourhood tabu (all quotient 2-switches, voltage changes and fixed-attachment moves, about 30k evaluations per
  step, tenure 12): 780 steps, stuck on a plateau at 80.
- ILS (kick 4 random moves, SA at T = 1, 20k steps, accept if not worse): 1309 iterations, never accepted a worse-or-equal
  state except one; best stays 80.
- focused moves (PFOCUS: edges touching the orbit of a witness far pair): no measurable gain at n=168 (105-129 either way).

## Later results (16:45Z - 17:10Z)

- Two-edge surgery (surg2.py: delete quotient edges i, j, add fixed A on bo1, fixed B on ao2 and one new quotient
  edge (ao1, bo2, t), or the mirror variant), all 19128 choices from the 3-fixed conder quotient to n=170: best 80
  already without repair (about 6 of them), next 83. Repairs of the 80 and 83 starts all end at exactly 80.
  Free quotient, same two-edge surgery to n=170 (16145 of 20580 evaluated before a timeout): best 105.
- Every one of the 112 order-3 elements of conder168 with 3 fixed vertices gives the same best single surgery (92),
  so there is essentially one seed in this family.
- Orbit insertion (py/orbit_ins.py): from the 3-fixed quotient (FA=3, FB=0), remove two fixed A-vertices, add a new
  regular A-orbit joined to their two B-orbits (voltages 9 choices), keep one fixed A-vertex and add one fixed
  B-vertex: n = 170 with FA = FB = 1, 27 candidates, direct costs 81; SA repair (55 s) gives 78 from both tried.
  File: c5/best170_far78.edges (verified by score37: far 78, diam 8). Best n = 170 of c5.
- Orbit insertion to n = 174 (py/orbit3.py, free quotient, delete 3 quotient edges, add a new A-orbit and a new B-orbit
  wired to the freed slots): 400 random candidates, best 183 direct; SA repair (60 s) gives 117 (c2 has 97 at 174).
- ILS from the far-78 state (821 iterations, kick 6, T 1.5): no improvement. Full tabu from the far-80 state: plateau.
- Far-80 graphs from different starts have identical far-count histograms (56 vertices with 0, 80 with 1, 24 with 2, 9 with
  3, 1 with 5) and no 4-cycles: all the repaired 80-graphs seem to be one structure.

## Where it stands (17:10Z)

Best in c5 family: n = 170, far 78 (c5/best170_far78.edges). Far below the board's 46 at n = 170 is not reached.
Order-3 fixed-point structures do not beat the non-symmetric surgery (c1 gives 46 from one 2-edge surgery + exhaustive
search). The 168 quotient calibration and the cost check are right, so the representation is usable for other seeds.
Plain SA on quotients cannot find 168 (random starts: 105-129), so this family needs a seed. Only conder168 is available
as a seed; its order-3 quotients give 80 (FA = 4, FB = 1) and 78 (FA = 1, FB = 1) at n = 170 after repair.

## Final (17:17Z)

- Repairs of 4 more orbit-insertion starts (o10_101, o18_200, o25_221, o12_110; direct cost 81) all end at 78; the 18
  direct-81 starts all look alike. Full tabu from the far-78 state: 600 steps at 78 (plateau). ILS from 78: no gain.
- Summary: conder168 seed in this family gives far 78 (FA=1, FB=1) and 80 (FA=4, FB=1) at n = 170. Best file:
  c5/best170_far78.edges (score37: n=170, far=78, diam=8). Not an improvement on the board's 46 at 170.
- Not done / next steps: a 168 seed other than conder168 (none found; plain SA fails at 168), or a larger-group
  (Z3 x Z3 / S3) structure around the fixed vertices; 174 via orbit insertion gave only 117.
- Scoreboard rows by c5: 170/80 (first c5 graph at 170), 170/78 (own improvement), plus one correction row (the
  correction row text is superseded by the clarification row).
- 17:24Z: last run, 7 min SA (13 runs, 50M moves, T 2 -> 0.4, PFOCUS 0.5) from the far-78 state: still 78.
  Stopping here. Best in c5: far 78 at n = 170 (c5/best170_far78.edges).
