# hunt-d5 squad, round 2: preamble (read ../r1/PREAMBLE.md first: problem, tools, machine rules, output format)

Same rules as round 1 (single thread, `timeout … nice -n 10`, about 12 CPU-minutes, 35 minutes wall clock, no git,
write only in your folder `research/squads/hunt-d5/r2/<card>/`). Scoreboard: `research/squads/hunt-d5/r2/scoreboard.jsonl`
(same one-line JSON format). Cells: (5,5), (7,5), (9,5), and new this round (6,5) (bipartite, Δ = 6, D = 5; the
published table value is 684 and we hold nothing there yet).

## Round 1 results (all cost > 0; do not repeat these runs)

- (5,5) Haar, orders 208–224 (60 groups): best 15 at SmallGroup(210,2), 16 at (216,161); orbit-symmetric S worse (40+).
  Lifts: 2+2 bases over 98–110, best 16 (SmallGroup(100,7), SmallGroup(104,3)); 3+3 bases over 65–75 with 1 s runs,
  best 30 (Z₆₅) — too short: flift needs > 5 s just to get near the known Z₅₉ record (cost 10–12 in 5–30 s);
  4+4 over 50–56 ≥ 65; 6+6 over 33–35 ≥ 82.
- (7,5) Haar, 30 groups of orders 608–630: best 12 at SmallGroup(624,134) (C13 : SL(2,3).C2), then 21; S₄ × Z₂₇
  (648): 13; orbit "3 2 1" worse. 5+5 lifts over 122–130: best 79; 6+6 over 101–108: 138; 7+7 and 11+11 lifts ≥ 149.
- (9,5) Haar: C197 ⋊ C7 = SmallGroup(1379,1): **8** (plain annealing, 20–40 s); C463 ⋊ C3 (1389): 10; other
  1378–1388 groups 18–512; orbit shapes "2 4 1", "4 2 1", "3 2 3" much worse; order 1392 has no order-3 automorphism
  with < 174 fixed points. 2+2 lift of C53 ⋊ C13 (689) with base [[2,7],[7,2]] (n = 2,756): 16 (30 s); 3+3 over 460–470
  ≥ 34; 4+4 over 346–351 ≥ 62.
- Route-chart lifts (director): a 3-letter chart over F₃⁴ with every non-backtracking pattern nonsingular and both
  pencil conditions exists (`../charts/chart_q3_u0.txt`). With it, **any** cubic bipartite controller with m + m
  vertices, same-side distance ≤ 4 and every vertex on a 4-cycle lifts to a (9,5) graph on 162·m vertices (checked:
  m = 12 → 1,944 and m = 16 → 2,592, apsp VALID). Controllers: m = 16 easy; **m = 17 stalls at cost 6** in three
  independent annealers; m = 18 at 8–12. The 4-cycles are needed because closed backtracking walks only cover ≤ 73 of
  the 81 fibre points. Non-abelian fibres (coset lifts over groups of order 81): worse.
- Dead: bi-coset graphs, lifts of PG(2,4) (girth 6 bases cannot give D = 5: the diagonal pairs need closed walks of
  length ≤ 4, i.e. 4-cycles or parallel edges in the base), free-voltage lifts of tripled controllers.

## New tools (research/squads/hunt-d5/tools/)

- `ctrl m SECONDS SEED OUT [sq|gen]` — cubic bipartite controllers (same-side ≤ 4; every vertex on a 4-cycle unless
  NO4=0). `ctrlpat m CHART SECONDS SEED OUT` — the same, aware of a chart's singular patterns (lines SINGA/SINGB in the
  chart file); DIAG4=1 (or DIAG4A=1 / DIAG4B=1 for one side) requires a nonsingular 4-cycle for the diagonal.
- `chartq q SECONDS SEED` — 3-letter charts over F_q⁴ (q = 2, 3, 4, 5); env DIAG=1 adds the diagonal condition (only
  possible for q = 2), WP / WD weights. Prints the chart and its singular patterns.
- `python3 rcq.py q CTRL CHART OUT.edges` — builds the lift (degree 3q) for apsp.
- `clift CTRL TABLE SECONDS SEED [OUT]` — coset lifts (each controller edge carries g⟨h⟩, h of order 3).
- `AUT=T.bin.autK ALINE=j ORBIT="k m f" haar5 exho T.bin d [LIMIT]` — **exhaustive** search over every S that is a
  union of the identity (f ≥ 1), f−1 α-fixed elements and m α-orbits of size k: prints every S with cost ≤ LIMIT and
  the exact minimum. Symmetric spaces are small (Δ = 7, k = 2: ~5M sets, seconds to minutes), so this certifies a
  group/α completely. `tools/exho_all.sh N I d "2 3 4 5 6"` runs it over every automorphism class of every listed
  order and every orbit shape (env TMO = seconds per run). The director is running it on SmallGroup(615,1) — skip that.

## Round-1 leads that are the starting points of this round

- **(7,5) SmallGroup(615,1): cost 4** (plain annealing, card b1); 609/1, 610/2: 8; 612/5: 9. Metacyclic-type groups
  (a cyclic normal subgroup with cyclic quotient, e.g. C41 ⋊ C15) lead in every cell, as in the earlier D = 5 runs.
- (7,5) 2+2 lifts over meta 61:5:9 (order 305) and meta 19:16:18 (304): 30.
