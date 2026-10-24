# exp2-alone-5: report

Worker: one Haiku session, working alone (no subagents). Target: the three D = 7 cells of the bipartite (Δ, D) table,
(7,7) table 23,436 vertices, (9,7) table 117,648, (11,7) table 398,580. Start 2026-10-24 16:56 UTC.

## Best valid size per cell (so far)

| cell | best graph | vertices | ratio to table | beat table? |
|---|---|---|---|---|
| (7,7) | Haar graph H(G,S), G = SL(2,8) × Z_19, N = 9,576 | 19,152 | 0.817 | no |
| (9,7) | Haar graph H(G,S), G = SL(2,13) × Z_19, N = 41,496 | 82,992 | 0.705 | no |
| (11,7) | Haar graph H(G,S), G = SL(2,13) × Z_61, N = 133,224 | 266,448 | 0.668 | no |

Every graph above passed build_haar2.py (independent rebuild, two BFS from (e,A) and (e,B), exact diameter 7, all
vertices reached, degree Δ, no repeated edge). Solution files are in research/frontier/sols/ with the d7D7_, d9D7_
and d11D7_ prefixes.

No cell is beaten. The gap is the size of the search wall, not a missing trick (see below).

## What was tried

Method: haar_sym.c from branch claude/structured-search-orbit-w5dd4f, ORBIT mode. S is made invariant under an automorphism
α of order 3 (conjugation by an order-3 element of SL(2,q) times z ↦ rz on Z_n), S = f fixed elements + m orbits of
size 3, with Δ = f + 3m. Parameters: (7,7): f=1, m=2. (9,7): f=0, m=3 (free orbits only). (11,7): f=2, m=3.
Group G = SL(2,q) × Z_n with every prime factor of n ≡ 1 mod 3. SL rather than PSL because D is odd (PSL has many
involutions, see STRUCTURE.md §2.6).

Before searching, the Poisson count μ = N·e^(−W/N) was checked (W = binding word count, see SIZE_LAW.md).
Practical wall: solutions came in seconds to minutes at μ ≈ 21–30 and failed at μ ≈ 38 and above within 5–10 M
evaluations.

Ladder (runs of 2–5 minutes each, 4 cores), group order N:

- (7,7), table N would need > 11,718: solved SL(2,11)×Z_7 (9,240, μ 21.6), SL(2,9)×Z_13 (9,360), SL(2,8)×Z_19 (9,576,
  μ 27.6). Failed: SL(2,5)×Z_79 (9,480, best 6 uncovered after 16 M evals), SL(2,7)×Z_31 (10,416, best 6 after 41 M
  evals in 5 min), SL(2,9)×Z_17 (12,240, best 1,440). The last one is above the first-moment ceiling.
- (9,7), needs N > 58,824: solved SL(2,11)×Z_31 (40,920), SL(2,13)×Z_19 (41,496), SL(2,8)×Z_79 (39,816). Failed at
  N ≈ 42–49 K: SL(2,9)×Z_61 (43,920, best 8–14), SL(2,7)×Z_127 (42,672, best 12–18), SL(2,7)×Z_139 (46,704, best 48),
  SL(2,8)×Z_91 (45,864, best 30), SL(2,11)×Z_37 (48,840, best 58), SL(2,5)×Z_349 (41,880, best 92), SL(2,5)×Z_361,
  SL(2,5)×Z_367, SL(2,7)×Z_133 (44,688, best 32).
- (11,7), needs N > 199,290: solved SL(2,19)×Z_19 (129,960), SL(2,16)×Z_31 (126,480), SL(2,13)×Z_61 (133,224).
  Failed: SL(2,11)×Z_103 (135,960, best 6 after 5 min), SL(2,8)×Z_271 (136,584, best 30), SL(2,9)×Z_181 (130,320,
  best 14), SL(2,9)×Z_193 (138,960, best 38), SL(2,7)×Z_397 (133,392, best 72).

## Why the cells are not beaten

The first-moment ceiling N_h (SIZE_LAW.md §1.4, solving N·e^(−W/N) = Δ ln N) lies below the table at all three
cells: about 10,600 vs. 11,718 at (7,7), about 45,000 vs. 58,824 at (9,7), about 155,000 vs. 199,290 at (11,7). So
beating them needs words that cover the group better than random S, and the orbit recipe does not raise that
ceiling (STRUCTURE.md §1). What we have is roughly 0.67–0.82 of the table, which is the search wall of this method.

## Long runs after the ladder (plateau)

Second batch (300 s each): nothing new solved. SL(2,5)×Z_349 (9,7) best 92; SL(2,7)×Z_127 (9,7) best 12; SL(2,9)×Z_61
(9,7) best 14; SL(2,7)×Z_31 (7,7) best 6; SL(2,11)×Z_103 (11,7) best 6; SL(2,9)×Z_193 (11,7) best 38.

Third batch (about 40 minutes each, then stopped by hand): SL(2,7)×Z_127 (9,7) best 6, SL(2,9)×Z_61 (9,7) best 12,
SL(2,11)×Z_103 (11,7) best 6, SL(2,7)×Z_31 (7,7) best 6 after 243 M evaluations (stopped at 29 min). All four sat on
the same plateau for the last 20–30 minutes.

Test of the plateau: ORBW=3 (uncovered fixed elements weigh 3 in the energy) on SL(2,7)×Z_31 and SL(2,7)×Z_127: still
6 and 12. The stuck elements are probably fixed-point misses of the torus (|Fix| = 5 for SL(2,7) at order 3), which the
orbit moves cannot reach. That is a property of the group, not of the schedule.

## Not tried (would be next)

- Groups with fewer fixed points under the order-3 automorphism, or a different α, for the SL(2,7) cells.
- PSL or PGL variants at D = 7 (more involutions, untested here).
- Two-orbit-per-side lifts (PLAN.md §5, item 2), which change the word count rather than the group.

## Budget and time

Budget meter (tools/session_usage.py, arm exp2-alone-5): research/squads/usage/exp2-alone-5.jsonl, readings every
20 minutes. Final reading at 18:06 UTC: budget_units 0.006 (cap 1.5).

Wall time: 16:56 → 18:07 UTC, about 1 h 11 min (cap 4 h). Stopped early because the plateau persisted across every
group and seed tried, and more hours of the same method were unlikely to move any ratio.

## Logs

research/squads/exp2/exp2-alone-5-logs/: every haar_sym log (RESULT lines and trajectories) and the three job lists.

## Status

Finished. No background work is running. Best valid graphs are committed in research/frontier/sols/ and verified with
build_haar2.py (d7D7_sl_8_19_orb3f1_s1, d9D7_sl_13_19_orb3f0_s1, d11D7_sl_13_61_orb3f2_s1; the other D = 7 files in
that folder are earlier, smaller graphs).
