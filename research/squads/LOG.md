# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## Round 3, raise3-6-9 (branch claude/raise3-d6d9-round3-54sygo): new families screened, orbit search closed for psl 11 x 97

- Record to beat 127,296 (N 63,648); a new record needs N ≥ 63,649. Round 2's notes and EXHAUST mode carried over.
- Screened (orbit pairs, 10⁶-sample cost histograms): pgl twins (11×49, 13×31, 9×91), A5×PSL(2,13), A5×A5×Z19, A4×SL(2,3)×Z_p,
  A4×A5×Z91, sl/psl 7, 8, 9 with large n. Every PGL-type group has a much thinner low-cost tail than its SL/PSL partner;
  the products without a cyclic factor are weak or degenerate. tpgl does not run in orbit mode.
- Plain (non-orbit) annealing, 2·10⁶ evaluations: record group best 12; psl 11×97 best 35. Not a route at μ ≈ 30.
- ORBIT="6 1 0" (single orbit of size 6): only odd prime k is auto-picked; on the two groups that ran, nearly all samples uncovered. Dead end.
- Exhaustive psl 11 × 97 (N 64,020): all 2.276·10⁸ orbit pairs checked, no pair below cost 15, no solution.
- Exhaustive psl 11 × 103 (N 67,980): started; result to be added to research/squads/cells/raise-d6D9.md.
- Record unchanged at 127,296. Details in research/squads/cells/raise-d6D9.md.
