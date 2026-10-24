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
2. (pending at time of writing; see below)
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
