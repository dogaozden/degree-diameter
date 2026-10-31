# w3 notes: lifts of W(3) (GQ(3,3) incidence graph, 80 vertices) over groups of order 63..80

Start: 2026-10-31 21:42 UTC. Planned end: about 23:42 UTC. Updated 22:35 UTC.

## Setup
- Base: `w3base.txt` (mkbase.py): points of PG(3,3) (0..39), totally isotropic lines (40..79), 160 edges. Checked:
  4-regular, girth 8, diameter 4.
- Lift over G: vertex (v,x) = v*N+x, base edge (eu,ev) with voltage g gives (eu,x) ~ (ev,g*x). Tree edges fixed to identity,
  81 cotree voltages free. n = 80 N, so n > 4,970 needs N >= 63 (n = 5,040). Only the four groups of order 63 matter for
  a record: Z_63, Z_3 x Z_21, Z_7 x| Z_9 (meta 7 9 2), (Z_7 x| Z_3) x Z_3.
- Cost = sum over base roots u, targets w, elements x with no walk of length <= 9 (parity fixed) and voltage x, i.e.
  ordered far pairs with a root in fibre 0, scaled: far unordered pairs = cost * N / 2 (checked: cost 906 <-> far 28,539).
- Walk facts (checked, walkcount.py, distinct.py): every same-side target gets 244 non-backtracking walks of length <= 8
  (324 for the root itself); cross targets get 730 or 811 walks of length <= 9. All 244 walks have distinct signed
  dart-count vectors (no abelian degeneracy). Mass per element is 3.9 at N = 63, so no counting obstruction.

## Tools (all in this folder)
- `w3s` (w3s.c): one program. `w3s BASE GROUP eval VOLTFILE`, `w3s BASE GROUP anneal SECS SEED OUT [VOLT]`,
  `w3s BASE GROUP repair SECS SEED OUT [VOLT]`. GROUP = cyc:N or tab:FILE.bin (tabs/ has the four order-63 tables).
  Env SYM=sym5.txt imposes invariance under a base collineation of order 5 (16 vertex orbits, 32 edge orbits; made by mksym.py).
  Repair = walk-directed moves: pick a missing (root, target, element), enumerate non-backtracking walks to the target,
  solve for the voltage each walk needs, evaluate a sample of 60 candidates with the full cost, SA acceptance (RT).
  Cost 0 writes OUT_c0.edges (lift edge list, check with apsp).
- Older programs w3lift.c / w3rep.c are superseded by w3s.c.

## Results (cost = missing triples; lower is better; random start is about 4,000 at N = 63)
| group | N | method | secs | best cost |
|---|---|---|---|---|
| cyc 40 | 40 | repair | 60 | 0 (VALID n=3200, apsp checked: runs/rep40b_c0.edges) |
| cyc 40 | 40 | SA | 30 | 30 |
| cyc 48 | 48 | SA / repair | 40 / 60 | 122 / 87 |
| cyc 56 | 56 | SA / repair | 40 / 60 | 423 / 412 |
| cyc 60 | 60 | SA | 40 | 748 |
| cyc 63 | 63 | SA hot (T0 6) | 60 | 1004 |
| cyc 63 | 63 | repair (RT 1, 150 s) | 150 | 906 (far pairs 28,539; runs/rep63_best.volt) |
| cyc 63 | 63 | repair (RT 1.5) | 130 | 990 |
| cyc 63 | 63 | repair with SYM order 5 | 130 | 1030 |
| cyc 63 | 63 | SYM order 5 SA | 110 | 1150 |
| Z3 x Z21 | 63 | SA / repair | 80 / 130 | 1130 / 1134 |
| Z7 x| Z9 | SA / repair | 80 / 130 | 1092 / 1176 |
| (Z7 x| Z3) x Z3 | 63 | SA / repair | 80 / 130 | 1066 / 1002 |

Warm-start repair from the 906 state for 200 s did not improve it.

## Conclusion so far
- The family has a sharp threshold: diameter 9 is reached at N = 40 (n = 3,200) in under a minute, but the best
  search reaches only about 900 at N = 63 (a random lift has about 4,000). Costs rise steadily with N, so n = 5,040 is far.
- Walk counts are not the obstruction (mass 3.9 per element with >= 244 walks per target). The floor comes from the number
  of independent constraints (80 roots x 40 targets x N), which grows with the base size while the variables do not.
  Two-vertex bases (Haar graphs) hit the same mass ratio with far fewer constraints, which fits the record search.

## Next, if I had more time
- Lifts with more structure than an order-5 collineation (e.g. a Z_3 x Z_3 or a group of order 10-15 of base automorphisms)
  to cut the constraint count, or base graphs with fewer vertices (a 40-vertex 4-regular bipartite base over order 126).
- A tabu search with the full 1-move neighbourhood in the 32-variable symmetric space (about 2,000 neighbours per step).
