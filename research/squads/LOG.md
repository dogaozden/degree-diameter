# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-24, beat-16-5-squad (session_01R83cdF9zMzt8oY4YvTTqZc), goal: (16,5) bipartite > 31,460 — round 1 (04:40–05:10 UTC)

Lead going in (Opus, solo, first ~75 min): the bipartite "controller lift" (Mizuno's route chart made bipartite,
research/theorems/BEAT_16_5_SQUAD.md §2). A 4-regular bipartite controller with m vertices per side and the exact-NB-4
property lifts to a 16-regular bipartite graph on 512m vertices with diameter ≤ 5, so m ≥ 62 beats the record. Best
before the round: m = 42 (Haar, Z₇⋊Z₆), lift 21,504 verified by apsp. Also done solo: all Weyl-distance graphs of all
finite buildings (only the flag graph has D = 5 above 15,000).

Cards (folders research/squads/r1-165/c1..c8):
1. Haar controllers over non-metacyclic groups of order 62–72.
2. Haar controllers over non-metacyclic groups of order 73–108.
3. 2-orbit controllers (voltage lifts of 2+2 bases).
4. Repair near-miss controllers (m = 63 cost 2) by local search.
5. Controllers as lifts of K₄,₄ (4+4) and K₃,₃ + doubled matching (3+3).
6. Wildcard: literature (the 27,300 construction, newer (16,5) values, 2024–2026 papers).
7. Wildcard: anything plausible not yet ruled out.
8. Wildcard: subgroup-invariant graphs on PG(4,3) flags beyond Weyl distances.

Outcomes (cost = uncovered elements or pairs; 0 = perfect controller):
1. worse: 129 non-metacyclic groups (98 of order 64, 31 of order 72), exhaustive over S. Best cost 8 at m = 64,
   10 at m = 72; no perfect. (Orders 62, 63, 65–71 have only metacyclic groups.)
2. worse: 321 group tables of orders 73–108 (121 signature-distinct non-metacyclic groups plus non-split metacyclic
   ones such as Q₈×Z₁₁), exhaustive over S. No perfect controller; best Z₅²⋊Z₃ (m = 75) at cost 10.
3. better than Haar, no hit: 2-orbit lifts perfect up to m = 48 (Z₂₄, Z₆⋊Z₄); exact floors 8 (Z₃₁, m = 62) and
   9 (Z₈⋊Z₄, m = 64).
4. no hit: exhaustive 2-orbit abelian lifts floor at 8 (Z₃₁) and 12 (Z₃₂); the plain switch-anneal from the m = 63
   Haar near miss does not move.
5. **best of the round**: K₃,₃ + doubled matching lifted by Z₁₈ is a perfect controller at **m = 54** (new best,
   above Haar's 42); its lift has 27,648 vertices, apsp VALID d=16 D=5 (Haiku's check; Opus re-ran it with an
   independent annealer, mlift.c, and apsp: VALID). Floor 6 at m = 63 (Z₂₁, Z₇⋊Z₃). K₄,₄ lifts: perfect only to m = 40.
6. (pending)
7. no hit: 65 further groups of order 62–108 (affine, products, SL(2,3)×Z_k, ...); best cost 8 (D₈×Z₃×Z₃, m = 72).
8. failed: Singer-invariant surgery adding the 121 solids as a new orbit (31,581 vertices) leaves ≥ 77,844 pairs at
   distance > 5; deleting one edge orbit already breaks 1,098 pairs per vertex. The flag graph has no slack.

Kept: the orbit direction (more orbits → bigger perfect controllers: 42, 48, 54 for 1, 2, 3 orbits). Next (Opus):
exhaustive sweep of all 6 bases on 3+3 and all 26 on 4+4 with groups of order m/k for m = 62–72 (mlift.c), then
round 2 on bigger bases (5+5 … 8+8), nonabelian groups and exhaustive/SAT search on the best (base, group) pairs.

## 2026-10-24, beat-16-5-squad (session_01R83cdF9zMzt8oY4YvTTqZc) — round 2 (05:40–06:30 UTC)

Lead going in: the pencil lemma (BEAT_16_5_SQUAD.md §2.1). With a pencil-complete chart, distance-2 controller pairs
are free, so a controller needs only diameter ≤ 5, a nonsingular 4-cycle at every vertex and nonsingular NB-4 walks
for distance-4 pairs. Tool: mlift_chart.c (fixed charts chart_p4/p5, 12 singular patterns each). Also found by Opus
just before the round, from round-1 card 6's lead: the bipartite double cover of the LANL (16,4) graph gives
**32,768** (verified twice). It is someone else's graph, so the target for a construction of our own became m ≥ 65.

Cards (folders research/squads/r2-165/c1..c8):
1. 3+3 bases, groups of order 21/22 (m = 63/66), 16 pattern files.
2. 4+4 bases, groups of order 17/18 (m = 68/72).
3. many orbits: k = 5..8 and 13 random bases, small groups (m = 65–72).
4. 2+2 bases, groups of order 33–36 (m = 66–72), exhaustive.
5. a chart that is both universal and pencil-complete.
6. chart-aware Haar controllers, exhaustive over S, orders 62–80.
7. wildcard: m = 72–81 by any base/group.
8. wildcard: bipartite double covers of the current general (Δ,4) records for Δ = 10..15.

Outcomes:
2. no hit: best 8 at m = 68 (Z₁₇), 10 at m = 72 (Z₁₈); diagnosis: the 8 misses are exactly the 8 self-pairs
   (each orbit's identity vertex lacks a nonsingular 4-cycle); everything else is covered.
3. no hit: best 8 at m = 65 (k = 5, Z₁₃); costs grow with k.
4. no hit, exhaustive (all voltage tuples up to Aut(G)): floor 4 at m = 66–72 for every group; side result: a
   perfect 2-orbit controller at m = 52 (D₁₃), lift 26,624 apsp VALID.
7. no hit, but the key diagnosis: k3_000 (multiplicities (0,1,3),(1,2,1),(3,1,0)) with Z₂₄ at **m = 72** has cost 6,
   and the 6 misses are exactly the 6 self-pairs. All cross-orbit pairs are covered.
8. side result (not (16,5)): the double cover of Mizuno's (12,4) graph (5,832) is a bipartite (12,5) graph on
   **11,664** vertices, apsp VALID (table 8,200). Credit for the base graph is Mizuno's. Δ = 10, 11, 13, 14, 15
   covers have diameter 6–9.
1, 5, 6: pending at time of writing.

Kept: the self-pair diagnosis (cards 2 and 7, same as Opus's own at m = 63). Next (Opus): force a 4-cycle at every
orbit by tying parallel base edges with an involution (v(e′) = v(e)·h makes the digon walk e e′ e e′ trivial), which
needs even-order groups; then anneal the rest.
