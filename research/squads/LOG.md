# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-25 05:00-05:45 UTC, bigcheck-dist lead (Opus), round bcd-d8-r1

Goal: large diameter-8 cyclic lifts of H(5) + 2 extra edges per vertex (Δ = 8); score = copies M with cost 0.
Benchmarks: plain annealing (x2s) M = 16 solved, M = 20 cost 2; Delorme's structured construction M = 25;
M ≥ 31 would beat our (8,8) record. Brief: research/squads/bcd-d8-r1/BRIEF.md.

| card | idea | best |
|---|---|---|
| c1 | focused repair (min-conflicts) on failing pairs, copy of x2s | M = 22 cost 102 (not better than annealing) |
| c2 | algebraic incidence voltages (bilinear forms, positions, GF(5) formulas) | no family better than random (M = 20: cost 34 after annealing) |
| c3 | Z_5 × Z_k product (lifts of the D = 7 graph X_2) | k = 4 (20 copies) cost 30, k = 5 cost ~1000: harder than plain lifts |
| c4 | placements of the extra edges (random, parallel, τ-shifted, fixed distance 1/3/5) | two independent random bijections best; doubled incidences worst |
| c5 | torus + Frobenius symmetry | impossible: Frobenius elements fix 6 points and no line |
| c6 | point-point / line-line jumps with a parity layer | worse per copy (2M = 16 cost 10 random) |
| c7 | genetic algorithm; random sampling | **M = 17 valid** (132,804 vertices; lead re-checked with bcd: VALID, diameter 8) |
| c8 | provable rainbow construction (Δ = q+2, q+3 copies) | the needed 7-colouring of H(5) not found (SAT 15 min, tabu stalls) |

Kept: nothing beats plain annealing; the gap to Delorme (20 vs 25 copies at q = 5, ~18 vs 30 at q = 7) is
structural, not compute. Next: theory (an Opus agent on reconstructing Delorme's family), and a Haar orbit search for
(10,8) instead (research/projects/bigcheck-dist/HANDOFF.md). An honest "the squad added nothing new" for this goal.
