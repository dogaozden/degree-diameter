# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-24, cell-14-8 session (Opus), goal: beat (Δ,D) = (14,8) table value 14,172,480 — round 1 (r1_d14D8)

Context found first: the table value is 40·|H(11)| (Delorme–Gómez–Quisquater, credited on CombinatoricsWiki, which still
lists 14,172,480); every even-Δ D = 8 table value with Δ ≥ 10 is 5(q+5)/2·|H(q)|, q = Δ − 3 (two extra edges per vertex
on the split Cayley hexagon). Random and orbit Haar search cannot reach it (SIZE_LAW: table above the first-moment
ceiling). Shared tools: research/squads/cells/d14D8_work (H(q) builder, exact bitmask lift checkers). Cards, all on
cyclic/other lifts of H(q) + extra edges, scored by the lift checker:
- c1 bundle voltages from projective line parameters — (pending at log time)
- c2 reconstruct DGQ with quadratic labels / Z5×Zt splits — structured labels no better than uniform random; q = 11
  random reaches m = 14 (sampled 1,070 sources), q = 7 m = 10 all-source valid, m = 12 fails.
- c3 small-q annealing of all voltages — q = 3: m = 28 exact (all 364 sources; DGQ formula 20; re-checked by Opus);
  q = 5 stalls at exact cost ~900 for m = 20 (DGQ 25).
- c4 Singer-torus (C133 ⊂ SL(3,11)) symmetric designs — (pending)
- c5 H(13) minus a perfect matching plus a new one — (pending)
- c6 H(9) + 4 matchings — random hexagon voltages: frontier near m ≈ 50 (needs 107); r:200 fails at 56.
- c7 non-abelian / permutation voltages (dihedral, Heisenberg, affine) — no gain over cyclic; best exact m = 12 at q = 5.
- c8 GQ lifts — W(11) + 2 matchings, random Z_2000 voltages: exact all-source 5,856,000 vertices (0.41× table);
  W(13) alone Z_1000. Found a real bug in the shared checker: r:K:1 sampled only source 0 (seed 1 zeroed the RNG);
  fixed at 19:45 UTC and all cards told to re-check.
Kept: the lesson that every random-like design (any group, any base) stops at walks/target ≈ ln(#targets) (m ≈ 14 at
q = 11), while DGQ reaches 40 by exact structure. Next: structured / symmetric designs only.

## 2026-10-25 ~11:00 UTC, cell-14-8 resume (Opus, session_017UdGB4GF1FkF642zxrRdwH), goal: beat (14,8) = 14,172,480 = 40·|H(11)| — round 2 (r2_d14D8)

Opus first: the D = 8 bipartite problem is "every cross pair within 7"; the D = 7 table graph is 5 levels of H(q) with one
doubled bijection φ (+1, +2), and the D = 8 table is 8 = (q+5)/2 times that, so the round tested "D7 levels × Z_k" and
other STRUCTURED designs, scored exactly at q = 5 (table multiplier 25) and q = 7 (30; beating it would also be a (10,8)
record), with Σ-symmetry (Singer torus, new tool symq.py) for exact quotient costs. New tools: liftdiag (uncovered targets
by hexagon distance and level), nblev (exact non-backtracking walk counts per (distance, level) class).
- c1 Σ-symmetric annealing inside the D7 level family — no zero design: q = 5 k = 5 best exact cost 17,887; q = 7 k = 6
  cost 2.38M (random start 2.45M).
- c2 rainbow-bundle hexagon voltages (local search on bundle diversity) — diversity barely moves (3.69 → 3.69 distinct of
  5 per bundle at q = 5); lift costs equal to random h.
- c3 coordinate voltages (projective parameter, Singer index, ratio colours) — exact m = 12 (q = 5), 10 (q = 7), sampled
  12 (q = 11): the same as uniform random.
- c4 level-skeleton scan (183 structures, Z_L × Z_k) — random sub-voltages: exact m = 12 (q = 5), 6 (q = 7).
- c5 Σ-symmetric annealing in plain Z_m at q = 7 (1,032 reps, exact) — **exact m = 17** (random 12–13), stalls at 18.
- c6 geometric matchings (flag, distance 3, distance 5, equivariant, coordinate involution) — exact m = 11 (q = 5),
  10 (q = 7); flag-type φ worst.
- c7 wildcard: route families by construction — none beyond the level design; level 0 at distance 1, 3 is the bottleneck.
- c8 wildcard: non-abelian groups (dihedral, dicyclic, Frobenius, S4) — exact |G| = 12 at q = 5 and 7, like cyclic.
Opus check: nblev on the level skeletons. With random φ the D7 skeleton's worst class (level 0 at distance 3) has only
13–14 walks per target at q = 7 and 11 (the geodesic + 12 detour differences), the far classes 22–34; "balanced"
skeletons (2 levels, both jumps +1) have ~80 (q = 7) / ~122 (q = 11) per class and level. So the table graph, if it is
D7 × Z_8, hashes 14–31 walks onto 8 values almost perfectly; nothing we tried comes within a factor 2 of that.
Kept: nothing beats random by more than the annealing gain (×1.35 at q = 7). Squad added breadth (8 families ruled out
in 25 minutes) but no lead. Next: stop the cell unless a construction idea appears (see research/squads/cells/d14D8.md).
