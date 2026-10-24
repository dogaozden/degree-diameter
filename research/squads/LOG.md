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
