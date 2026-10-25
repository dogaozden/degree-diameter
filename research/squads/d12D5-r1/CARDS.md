# Round 1 (resumed session, Oct 25 ~14:20 UTC): cards

Context: per-edge charts (research/d12D5/EDGECHART.md) gave 10,692 (m = 66, K33m / Z_22) in one 300 s run.
Goal of the round: VALID lifts with m ≥ 67 (beat 10,692), ideally m ≥ 72 (11,664) or more.

- c1: controller ceiling map, k = 3: all 6 bases in bases3/ × groups of order 24, 25, 26, 27 with the FAKE chart (mlift_chart + charts/fake_univ.txt).
- c2: k = 4 (26 bases in bases4/) × groups of order 17, 18: fake-chart screen, then mlift_ejoint on the best.
- c3: k = 2 (base_k2_1..3) × groups of order 34..38: fake-chart screen, then mlift_ejoint on the best.
- c4: mlift_ejoint on K33m over Z_23 (m = 69) and Z_24 (m = 72), many seeds; WRITEBEST near misses checked exactly with apsp.
- c5: mlift_ejoint on K33m over the NON-abelian groups of order 24 (m = 72).
- c6: algorithm card: improve mlift_ejoint (gauge fixing, moves, restarts, temperature) and benchmark at m = 69.
- c7, c8: wildcards (an approach none of the other cards uses).
