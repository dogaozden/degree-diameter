# handsoff-108 digest (c2b-digest)

Last rewrite: 2026-11-01 02:27 UTC. Next (final) rewrite at 03:30 UTC, after the grinds stop. Target cell: Δ10, D8, more than 1,176,480 vertices
(Haar: N ≥ 588,241, |S| = 10). Numbers are copied from NOTES.md, scoreboard.tsv and log tails; units are as stated.

**CLAIMS OF COST 0 FOR THE TARGET CELL: NONE.** Two kinds of cost-0 numbers exist, and neither is in the target cell:
- scoreboard, c6-hexagon (voltage lifts of H(q) plus two matchings, Δ = q+3): 16,016 (Z22, H(3), Δ6), 17,472 (Z24, H(3), Δ6),
  54,600 (Z20, H(4), Δ7), 109,368 (Z14, H(5), Δ8), 117,180 (Z15, H(5), Δ8).
- c7b-design, scoreboard 02:24: "cost 0" at Δ6 (H(3) lift over Z30, 30 copies, verified by indep.c) and at Δ8 (H(5) lift over
  Z20, 20 copies, verified by indep.c). Earlier, c7b's runs/hz_summary_q3.txt has Δ6 "cost 0" at m = 12 to 24 (8,736 to 17,472 vertices).
The best exact cost in the coset families so far is 4 plain (family K, exhaustive) and then 44 plain (family C, A-root exhaustive,
B-pass in progress). Nothing is a record.

**Flags for the coordinator (found while digesting):**
1. RESOLVED. c6b-exhaust/run_all.sh was stopped before its C step (c6b NOTES); no duplicate family-C scan runs.
2. RESOLVED. c3b's screen.sh had waited forever for driver.done; c3b killed it and ran the eight RANDORB screens by hand
   (screen2.sh, seeds 108461-108468). All c3b runs are finished (c3b NOTES line 30; screen.done at 01:27).
3. RESOLVED. The c5c scoreboard line is now 44 (01:23), replacing the stale 530.
4. OPEN, not a claim: c1-grind g1 has three chains at minimum 9 (CHAIN 163, 211, 250 in g1.log). The scoreboard rule is ≤ 6.
5. RESOLVED (not a claim): c7b's cost-0 lines are now on the scoreboard (02:24), marked as not the target cell. Its Δ10 K = Z43 run is at cost 559 and not valid.
6. Worker folders not on the card list: c6c-h12 (coset families for h = 12; scoreboard 01:25, no NOTES.md yet) and
   c3c-grind (relaunch of slot c3 at 01:40; its own NOTES.md has the card; 24 chains at 01:57).
7. OPEN, not on the scoreboard: c6c-h12 D6nsq is complete (exact best 1266 plain; see its row). Not a record, not a claim.
8. OPEN, NEEDS THE SCOREBOARD: c1-grind g2 (prod psl 7 sl 8 7, seed 108201) chain 352 has minimum 6 (g2.log line 1247, about 02:20). The card asks for a scoreboard line for any chain min ≤ 6; none is written as of 02:25. It is above 3, so no EXDESC is required by the card.

## Status and key numbers

Units: ORBW=3 energy for every F15W3 descent (chain minimum = CHAIN field 4) unless stated. "plain" = uncovered vertices.
Reference for F15W3 on psl 23 × Z97 (c1 logs, same schedule): chain median 21; chains ≤ 9 about 1 in 15 (card).

| worker | card | status (01:57 UTC) | key numbers | main finding | cost-0 claim? |
|---|---|---|---|---|---|
| c1-grind | volume on psl 23 97 and prod psl 7 sl 8 7 | running: g1 pid 2553, g2 pid 3125, about 57 % CPU each; budget ends about 04:25 UTC | g1 (psl 23 97): 370 chains, min 9, median 21, ≤12: 14, ≤9: 3. g2 (prod psl 7 sl 8 7): 366 chains, min 6 (chain 352), median 21, ≤12: 8, ≤9: 1, ≤6: 1. Scoreboard: 15 (21:50), 12 (22:45); the min-6 chain is not on it yet (flag 8) | Lowest chains so far: 9 (g1, three times) and 6 (g2, once); no cost 0 | no |
| c1b-structure | what makes a good orbit set (random vs biased start A/B) | done (timeout, exit 124, about 01:24) | 70 chains: min 12, median 18, ≤12: 3. Random-start arm 35 chains: median 21, one ≤ 12. Biased-start arm 35 chains: median 18, two ≤ 12 | Medians differ by 3 but the tail counts (1 vs 2) do not; no separation at this sample size. c1b NOTES: 84-95 % of chain ends already reach c3 = 0 | no |
| c2-repair | two-orbit moves from the 119 good states | done (no processes) | 5 starts: 2 at energy 3 (psl), 3 at energy 6 (2 prod, 1 psl). K = 100; about 3 × 10^4 pair evaluations per state (c2 NOTES summary 00:37) | No 1-move or 2-move (K = 100) improvement for any start | no |
| c3-twist | twisted cyclic factor (tpgl, csl) | stopped early at 21:53 (no processes) | RANDORB: tpgl 23×Z49 median 345 vs sl 23×Z49 median 132. sl 23×Z49 F15W3: 6 chains, minima 18, 18, 24, 24, 27, 27 | tpgl is worse; csl with n ≡ 2 mod 4 is just SL(2,q)×Z_{n/2} | no |
| c3b-sl23x49 | descents on sl 23 × Z49, ORBW tests, RANDORB screen of other sl(q)×Z_n | done (no processes); screen.done 01:27 | d1 (ORBW=3, 4000 s): 88 chains, min 12, median 24, ≤12: 1, ≤9: 0. d2 (ORBW=2, 1200 s): 26 chains, min 17, median 23 (ORBW=2 units). d3 (ORBW=4, 1200 s): 24 chains, min 18, median 24 (ORBW=4 units). RANDORB=1000 (min / median): sl 13×Z271 49 / 306; sl 9×Z823 155 / 1198; sl 8×Z1171 155 / 1135; sl 7×Z1753 429 / 4375; sl 7×Z1777 526 / 4164; sl 7×Z1783 357 / 4548; sl 5×Z4903 4071 / 34362; sl 5×Z4921 3219 / 36657. Reference sl 23×Z49: 47 / 132 | sl 23×Z49 is not better than psl 23×Z97 (median 24 vs 21); the other sl(q)×Z_n in the window are far worse in RANDORB | no |
| c3c-grind | NOT on the card list: one more fresh-seed F15W3 grind on psl 23 97 (relaunch of slot c3; card in its NOTES.md) | running: g3 pid 31657, about 61 % CPU, started 01:37; card runs to 03:25 UTC | 63 chains: min 12, median 21, ≤12: 1, ≤9: 0 (log at 02:25). Seeds 108471-108480. Scoreboard 02:03: cost 12 | Same reference group as c1; no chain ≤ 9 yet | no |
| c8d-grind | NOT on the card list: second extra F15W3 grind on psl 23 97 (relaunch of slot c8; card in its NOTES.md) | running: g4 pid 6530, about 68 % CPU, started 02:15:54; scorer budget ends about 03:22:35, outer timeout 03:23:35 | 15 chains: min 18, median 21, ≤12: 0 (log at 02:25). Seeds 108981-108990 | Too early | no |
| c4-groups | screen of direct-product groups | done (descents.done; no processes) | 3850 candidate groups; 300-sample screen of 473 non-meta groups with n ≤ 5000. Top by (p1+p10)/2/μ: prod psl 7 pgl 8 ×Z7 (0.917), prod psl 7 sl 8 ×Z7 (0.932, grind group), psl 29 ×Z49 (0.959), sl 23 ×Z49 (0.959), psl 27 ×Z61 (1.035), psl 23 ×Z97 reference (1.048). Descents: psl 29×Z49 (d1): 40 chains, min 12, median 21, ≤12: 1. psl 27×Z61 (d2): 39 chains, min 21, median 27 | psl 29×Z49 matches the reference median and has a better screen score; psl 27×Z61 is worse; n > 5000 and meta groups are out (pilot medians 92k to 520k; meta n = 1: 3.4k to 569k) | no |
| c5-selfdual | twisted self-dual pairing S⁻¹ = β(S) | done (dead; no processes) | RANDORB min of 3000 (plain): psl 23×Z97 with inner β 125,257 (median 141,318); prod psl 5 × psl 27 with β inverting α 113 (median 1226). The β-2 prod run is invalid (β does not normalise α) | Dead: the ι-fixed elements and the Z-part kill the family | no |
| c5b-cosetscreen | screen of coset-graph families | done (no processes) | 14 round-1 families plus four extras (K2, C2, A2, K3). Family K = PSL(2,229), D5, one regular double coset: sample min 87, median 340 (n = 60); best sampled member full C = 55 plain (rep key 134144, 1,060 samples). Family C = PGL(2,181), D5 nonsquare: min 127, median 456 (n = 100). h = 6 families: min 101 to 1920 | Non-regular double cosets 3 to 10 times worse; square-reflection D5 and C10 in PGL(2,181) are disconnected | no |
| c5c-scanC | full scan of coset family C (PGL(2,181), D5 nonsquare) | done: A-root scan complete (16,407 classes, 59,202 members, 01:22); B-pass extension finished (scoreboard 02:14: family C exhausted) | Exact best C = 44 plain (uBA 44, uAA 0, uBB 0; classes 22786 and 37938; scoreboard 01:23). Every class has P = uBA+uAA ≥ 44, so 44 is the family minimum. Exact top 10 (scoreboard 02:14): 44, 44, 63, 63, 63, 63, 65, 65, 71, 71 | Family C has no cost 0; its minimum is 44 plain | no |
| c6-hexagon | structured lifts of H(q) | done (no processes) | Valid lifts (Δ < 10 only): q=3 Z22 (16,016), q=3 Z24 (17,472), q=4 Z20 (54,600), q=5 Z14 (109,368), q=5 Z15 (117,180). q=5 Z16 not reached. q=7 evaluation about 1 min | Annealed lifts work for q ≤ 5 only; nothing at Δ10 | no for the target cell (see top) |
| c6b-exhaust | exhaustive scan of coset family K (PSL(2,229), D5, one regular double coset) | done: all 16,293 classes (59,985 members); no processes | Exact best C = 4 plain (class 4233; uBA 4, uAA 0, uBB 0). Exact top 10: 4, 33, 37, 41, 42, 45, 45, 46, 47, 50 (c6b NOTES). Scoreboard 00:51 (cost 4, "not diameter 8"). Not yet checked independently by the coordinator | Family K has no cost 0; its minimum is 4 plain | no |
| c6c-h12 | NOT on the card list: coset families for h = 12 over PGL(2,193) (N = 599,072 if the group is PGL(2,193)) | running D6sq (partition 6,2,2) scan: pid 5673 under run_d6sq622.sh, timeout 3300 s from about 02:12. Done: A4 (scoreboard 01:25) and D6nsq (rc 0 at 01:56) | A4 ≤ PGL(2,193): all 13,797 degree-10 double-coset sets (types 6+4 and 4+4+1+1): exact best 501 plain. D6nsq: 15,888 classes, 27,408 members, complete: exact best 1266 plain (partition 6+2+2), median per member 8112 | Both h = 12 families are poor; their own notes say the single-regular-double-coset premise is wrong for h = 12 | no |
| c7-throughput | more good descents per CPU-hour | stopped (checked 00:43; no processes) | Chains ≤ 12 per arm: v0 (reference) 2/35; v1 (COOL 7.5) 0/40; v2 (COOL 30) 2/19; grind 5/245 (wall clock). Chain minima: v0 3, v1 15, v2 9 | No schedule separates on the ≤ 9 / ≤ 12 tail at this sample size; COOL 7.5 and 30 give about 1.5 to 1.8 times more chains at ≤ 15 per CPU-hour | no |
| c7b-design | structure in the annealed hexagon lifts; K-symmetric lifts | done (NOTES.md, 151 lines); no processes at 02:24 | Matching-only runs (hexagon voltages 0), q = 3: cost 0 at m = 12, 16, 20, 24; cost 28 at m = 28; 322 at m = 32; 1271 at m = 36. Scoreboard 02:24: K = Z30 lift of H(3) at Δ6, cost 0, 30 copies (table 20); K = Z20 lift of H(5) at Δ8, cost 0, 20 copies (table 25); K = Z43 lift of H(7) at Δ10, best cost 559, not valid (13 orbit units, 20 copies, table 30). Scoreboard 01:10: first-moment calibration (1,222,240 vs predicted 1,228,000 walk triples at m = 30) | Mixed: cost-0 lifts only at Δ6 and Δ8 (not target); no valid Δ10 lift from the K-symmetric family; c7b NOTES section 5: the table's 30 copies at q = 7 need structure | no for the target cell (see top) |
| c8-wild | coset graphs (Haar alternative) | done (no processes) | PGL(2,181) D5, one double coset: min 150 (40 candidates). PSL(2,181) C5, two double cosets: best 57 plain (60 random) | Coset graphs look about 3 times worse than Haar k = 3 descents (c8c notes) | no |
| c8b-coset | fast coset evaluator and annealer (PSL(2,181), C5) | done (processes stopped) | Best 45 plain (9 units of 5), 21 chains, median chain minimum about 57 plain. Scoreboard lines 76 and 39 were invalid (corrected to 166). Symmetric pairs: min 431 (6,164 pairs) | No cost 0; coset annealing does not beat Haar | no |
| c8c-smooth | smoother objective for the k = 3 annealer | running: SMOOTHW=2 arm (pid 32568, timeout 3000 s from about 01:42). SMOOTHW=1 arm done 01:30:57 | Base arm (ORBW=3, done): 29 chains, min 9, median 18, ≤12: 3, ≤9: 1. SMOOTHW=1 arm (done): 30 chains, min 6 (one chain, true energy), median 18, ≤12: 2, ≤9: 1. SMOOTHW=2 arm (so far): 16 chains, min 12, median 21, ≤12: 2. Scoreboard 01:04 (cost 6) | No separation yet; one chain at 6 is not significant | no |

## Leads worth more CPU

0. c1-grind g2 chain 352 (prod psl 7 sl 8 7, min 6): needs its scoreboard line (flag 8).

1. psl 23 × Z97 F15W3 (c1-grind and c3c-grind). Still the lowest tail: 3 chains at 9 and 20 at ≤ 12 in 659 descents of c1
   (g1.log lines 576, 744, 883 for the 9s). c3c-grind adds fresh seeds 108471-108480 on the same group.
2. psl 29 × Z49 (c4-groups d1.log): RANDORB score 0.959 against 1.048 for the reference (c4 NOTES table, ranks 3 and 7).
   Descents so far: 40 chains, median 21, min 12 (one chain ≤ 12). Same median as the reference on a different group, with the
   best screen score among the non-grind groups that were descended. Sample is small; a longer run is the test.
3. Family K member class 4233 (C = 4 plain, c6b NOTES): the exhaustive minimum of family K. Not a cost 0, not diameter 8.
   No local search has been run from it, and the coordinator's independent check is pending. Haar energy-3 states use
   ORBW=3 units, so the two numbers are not directly comparable.
4. c5c B-pass extension and c6c-h12 D6sq: still running; they can only lower the family minima they cover.
5. c8c smooth objective: 30 chains in the SMOOTHW=1 arm against 29 in the base arm, no difference yet; the SMOOTHW=2 arm is running.

## Dead ends

- c2-repair: no 1-move or 2-move (K = 100) from the 5 good states lowered the energy (c2-repair/NOTES.md, summary 00:37).
- c3-twist: tpgl twists are worse (RANDORB median 345 vs 132 for sl 23×Z49, c3-twist/NOTES.md).
- c3b-sl23x49: sl 23×Z49 descents not better than psl 23×Z97 (median 24 vs 21, 88 chains at ORBW=3). The other sl(q)×Z_n
  of the window: RANDORB medians 306 (sl 13×Z271) to 36,657 (sl 5×Z4921).
- c4-groups: groups with n > 5000 (pilot medians 92k to 520k) and meta groups (n = 1 pilots median 3.4k to 569k).
  psl 27 × Z61 descents: median 27 (39 chains).
- c5-selfdual: iota-pairing family (scoreboard 22:11): psl 23×Z97 min 125,257 plain; prod psl 5 × psl 27 min 113 plain,
  median 1226 (3000 samples each).
- c5b-cosetscreen: h = 6 families (PSL(2,193) C6 and S3, PGL(2,193) D6): sample minima 101 to 1920 plain; non-regular
  double cosets 3 to 10 times worse.
- c5c-scanC / c6b-exhaust: the one-double-coset families C (min 44) and K (min 4) are exhausted at the A-root level; no zero.
- c6c-h12: h = 12 families A4 (exact best 501) and D6nsq (exact best 1266) are both far worse than the h = 10 families.
- c6-hexagon: annealed lifts at q = 7 hopeless (one evaluation about 1 min); lifts at q ≤ 5 do not reach Δ10.
- c7b-design: no formula family beat random voltages (c7b NOTES).
- c7-throughput: no schedule separates on the tail (0 to 2 per arm).
- c8-wild / c8b-coset: coset annealing best 45 plain (9 units of 5), median chain minimum about 57 plain.
