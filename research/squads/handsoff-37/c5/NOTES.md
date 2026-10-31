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
