# handsoff-108 digest (c2b-digest), final

Last rewrite: 2026-11-01 03:28 UTC (final; the grinds stopped before 03:26, no search process is alive).
Target cell: Δ10, D8, more than 1,176,480 vertices (Haar: N ≥ 588,241, |S| = 10). Numbers are copied from NOTES.md,
scoreboard.tsv, summary files and log histograms (c2b-digest/hist.sh, field 4 of CHAIN lines). Units as stated.

**CLAIMS OF COST 0 FOR THE TARGET CELL: NONE.** The scoreboard has 8 cost-0 lines, none in the target cell:
- c6-hexagon (voltage lifts of H(q) plus two matchings, Δ = q+3): 16,016 (Z22, H(3), Δ6), 17,472 (Z24, H(3), Δ6),
  54,600 (Z20, H(4), Δ7), 109,368 (Z14, H(5), Δ8), 117,180 (Z15, H(5), Δ8).
- c7b-design (scoreboard 02:24 and 02:44): lifts at Δ6 (H(3) over Z30, 30 copies) and Δ8 (H(5) over Z20, 20 copies;
  H(5) over Z21, 21 copies), each verified by indep.c. The Δ10 K = Z43 lift of H(7) is at cost 559 and not valid.
Best exact costs in the one-double-coset families (plain): K = 4 (exhaustive), C = 44 (exhaustive). The best Haar chain
minimum is 3 (c7 reference, energy-3 state, ORBW=3 units). Nothing is a record.

**Flags for the coordinator:**
1. OPEN, NEEDS THE SCOREBOARD: c1-grind g2 (prod psl 7 sl 8 7, seed 108201), chain 352 has minimum 6 (g2.log line 1247,
   about 02:20). The card asks for a scoreboard line for any chain min ≤ 6. None is written (last c1 line 22:45).
2. OPEN, not a claim: c1-grind g1 has six chains at minimum 9 (none ≤ 6). Not on the scoreboard (rule ≤ 6).
3. RESOLVED: c6b's run_all.sh was stopped before its C step (no duplicate family-C scan).
4. RESOLVED: c3b's screen.sh had waited forever; c3b ran the eight RANDORB screens by hand (screen.done 01:27).
5. RESOLVED: the c5c scoreboard line is 44 (01:23), replacing 530; family C is complete (scoreboard 02:14).
6. RESOLVED: c7b's cost-0 lines are on the scoreboard, marked as not the target cell.
7. Worker folders not on the card list: c6c-h12 (h = 12 families; scoreboard 01:25 and later), c3c-grind (relaunch of slot c3,
   01:37 to 03:25), c8d-grind (relaunch of slot c8, 02:15:54 to before 03:26). Each has its own NOTES.md.
8. OPEN, not on the scoreboard: c6c-h12 D6nsq (exact best 1266) and D6sq (exact best 900) are complete. Not records.

## Status and key numbers (final)

Units: ORBW=3 energy for every F15W3 descent (chain minimum = CHAIN field 4) unless stated. "plain" = uncovered vertices.
Reference for F15W3 on psl 23 × Z97: chain median 21; chains ≤ 9 about 1 in 15 (card).

| worker | card | status at 03:26 UTC | key numbers | main finding | cost-0 claim? |
|---|---|---|---|---|---|
| c1-grind | volume on psl 23 97 and prod psl 7 sl 8 7 | done: no process alive at 03:26 | g1 (psl 23 97): 448 chains, min 9 (6 chains), median 21, ≤12: 18. g2 (prod psl 7 sl 8 7): 442 chains, min 6 (chain 352), median 21, ≤12: 10, ≤9: 2. Scoreboard: 15 (21:50), 12 (22:45) | Lowest tails of the squad (psl 9, prod 6); no cost 0; prod chain 352 not on scoreboard (flag 1) | no |
| c1b-structure | random vs biased start (A/B) on psl 23 97 | done (timeout 5400 s, about 01:24) | 70 chains: min 12, median 18, ≤12: 3. Random arm 35 chains (median 21, one ≤ 12); biased arm 35 (median 18, two ≤ 12) | No separation at this sample size | no |
| c2-repair | two-orbit moves from the 119 good states | done | 5 starts (2 at energy 3, 3 at energy 6); K = 100; no improvement | Dead | no |
| c3-twist | twisted groups tpgl and csl | stopped early, 21:53 | RANDORB median: tpgl 23×Z49 345 vs sl 23×Z49 132; sl 23×Z49 F15W3 chain minima 18, 18, 24, 24, 27, 27 | tpgl worse; csl with n ≡ 2 mod 4 is SL×Z_{n/2} | no |
| c3b-sl23x49 | descents on sl 23×Z49 (ORBW 2, 3, 4); RANDORB of other sl(q)×Z_n | done (screen.done 01:27) | d1 (ORBW=3, 4000 s): 88 chains, min 12, median 24, ≤12: 1, ≤9: 0. d2 (ORBW=2): 26 chains, min 17, median 23. d3 (ORBW=4): 24 chains, min 18, median 24. RANDORB (min / median): sl 13×Z271 49 / 306; sl 9×Z823 155 / 1198; sl 8×Z1171 155 / 1135; sl 7×Z1753 429 / 4375; sl 7×Z1777 526 / 4164; sl 7×Z1783 357 / 4548; sl 5×Z4903 4071 / 34362; sl 5×Z4921 3219 / 36657. Reference sl 23×Z49: 47 / 132 | sl 23×Z49 is not better than psl 23×Z97 (median 24 vs 21); the other sl(q)×Z_n are far worse | no |
| c3c-grind | psl 23 97 grind, seeds 108471-108480 (relaunch of slot c3) | done: 01:37 to 03:25 | 137 chains: min 12, median 21, ≤12: 3, ≤9: 0. Scoreboard 02:03: cost 12 | Same group as c1; no chain ≤ 9 | no |
| c4-groups | screen of 3,850 direct-product groups; descents on two groups | done | Screen top by (p1+p10)/2/μ: prod psl 7 pgl 8 ×Z7 (0.917), prod psl 7 sl 8 ×Z7 (0.932, grind group), psl 29 ×Z49 (0.959), sl 23 ×Z49 (0.959), psl 27 ×Z61 (1.035), psl 23 ×Z97 reference (1.048). Descents: psl 29×Z49: 40 chains, min 12, median 21, ≤12: 1. psl 27×Z61: 39 chains, min 21, median 27 | psl 29×Z49 has the reference median and the better screen score; psl 27×Z61 is worse; n > 5000 and meta groups are out | no |
| c5-selfdual | twisted self-dual pairing S⁻¹ = β(S) | done (dead) | RANDORB min of 3000 (plain): psl 23×Z97 inner β 125,257 (median 141,318); prod psl 5 × psl 27 with β inverting α 113 (median 1226). β-2 prod run invalid | Dead | no |
| c5b-cosetscreen | screen of about 18 coset-graph families | done | Family K (PSL(2,229), D5, one regular dc): sample min 87, median 340 (n = 60); best sampled full C = 55 plain (1,060 samples). Family C: min 127, median 456 (n = 100). h = 6 families: min 101 to 1920 | Superseded by the exhaustive scans; non-regular dc 3 to 10 times worse | no |
| c5c-scanC | exhaustive scan of coset family C (PGL(2,181), D5 nonsquare) | done: 16,407 classes, 59,202 members; scanB done 02:13 | Exact min 44 plain (classes 22786 and 37938; uBA 44, uAA 0, uBB 0). Exact top 10: 44, 44, 63, 63, 63, 63, 65, 65, 71, 71 | Family C exhausted; no zero | no |
| c6-hexagon | annealed voltage lifts of H(q) + 2 matchings, q = 3, 4, 5 | done | Valid lifts (Δ < 10 only): q=3 Z22 (16,016), q=3 Z24 (17,472), q=4 Z20 (54,600), q=5 Z14 (109,368), q=5 Z15 (117,180). q = 5 Z16 not reached; q = 7 about 1 min per evaluation | Works for q ≤ 5 only; nothing at Δ10 | no for the target cell (top) |
| c6b-exhaust | exhaustive scan of coset family K (PSL(2,229), D5, one regular dc) | done: 16,293 classes, 59,985 members (00:51) | Exact best C = 4 plain (class 4233; uBA 4, uAA 0, uBB 0). Exact top 10: 4, 33, 37, 41, 42, 45, 45, 46, 47, 50. Not yet checked independently | Family K has no cost 0 | no |
| c6c-h12 | coset families for h = 12 over PGL(2,193) (N = 599,072) | done: A4 (01:25), D6nsq (01:56), D6sq (rc 0, 02:40) | A4: 13,797 sets, exact best 501. D6nsq: 27,408 members, best 1266. D6sq: 40,480 members, best 900 (all plain) | All far worse than K and C | no |
| c7-throughput | schedules (COOL 7.5, COOL 30) vs reference on psl 23 97 | stopped (00:43) | Reference v0: 35 chains, min 3, median 18, ≤12: 2. v1 (COOL 7.5): 40 chains, min 15, median 18, ≤12: 0. v2 (COOL 30): 19 chains, min 9, median 18, ≤12: 2 | No schedule separates on the tail at this size | no |
| c7b-design | structure in annealed H(q) lifts; formula families; K-symmetric lifts | done (NOTES 151 lines) | Matching-only (hexagon voltages 0), q = 3: cost 0 at m = 12, 16, 20, 24; 28 at m = 28. K-symmetric: Δ6 H(3) Z30 cost 0 (30 copies, table 20); Δ8 H(5) Z20 cost 0 (20 copies) and Z21 cost 0 (21 copies, table 25); Δ10 H(7) K = Z43 best 559, not valid (table 30) | Cost 0 only at Δ6 and Δ8 (not target); no formula family beat random voltages | no for the target cell (top) |
| c8-wild | non-Haar coset graphs, PSL(2,181) C5 and PGL(2,181) D5 | done | PSL(2,181) C5, two dc: best 57 plain (60 random). PGL(2,181) D5, one dc: min 150 (40 candidates) | About 3 times worse than Haar k = 3 | no |
| c8b-coset | fast coset evaluator and annealer on PSL(2,181) C5 | done | Best 45 plain (9 units of 5); 21 chains; median chain minimum about 57 plain; symmetric pairs min 431 (6,164 pairs) | Coset annealing does not beat Haar | no |
| c8c-smooth | smooth term F/1000 in the k = 3 annealer; A/B | done (SMOOTHW=2 arm ended about 02:32) | Base: 29 chains, min 9, median 18, ≤12: 3, ≤9: 1. SMOOTHW=1: 30 chains, min 6 (true energy), median 18, ≤12: 2, ≤9: 1. SMOOTHW=2: 16 chains, min 12, median 21, ≤12: 2 | No separation; the single chain at 6 is not significant | no |
| c8d-grind | fresh F15W3 grind on psl 23 97, seeds 108981-108990 (relaunch of slot c8) | done: 02:15:54 to before 03:26 | 88 chains: min 12, median 21, ≤12: 2, ≤9: 0 | Same group as c1; no chain ≤ 9 | no |
| c2b-digest | this digest | done | no search run | n/a | no |

## Leads worth more CPU

1. Prod psl 7 sl 8 ×Z7 chain 352 (min 6, c1 g2) and psl 23 ×Z97 (c1 g1, six chains at 9): the grinds with the lowest tails.
   Neither reached ≤ 3, so the card's EXDESC step does not apply. The min-6 chain needs its scoreboard line (flag 1).
2. psl 29 × Z49 (c4 d1.log): screen score 0.959 vs 1.048 for the reference; median 21 over 40 chains. Weak, small sample.
3. Family K member class 4233 (C = 4 plain): the exhaustive minimum of K. Not a cost 0 and not diameter 8. No local search
   has been run from it. The coordinator's independent check is pending.

## Dead ends

- Coset families: K exhaustive (min 4), C exhaustive (min 44), h = 12 families A4 (501), D6nsq (1266), D6sq (900), sampled
  families of c5b (min 55 in K sample), c8/c8b (min 45 plain). No zero.
- Twisted and self-dual Haar families: tpgl (c3), sl 23×Z49 and the other sl(q)×Z_n (c3b), iota pairing (c5).
- Groups with n > 5000 and meta groups (c4 screen).
- Voltage lifts: valid only at Δ ≤ 8 (c6, c7b); K-symmetric Δ10 best 559 (c7b).
- c2 two-orbit moves (K = 100) and c7 schedule changes: no improvement or no separation.

## Final table for REPORT.md

Structure = the graph or base graph the worker computed on (2N = vertices of the Haar graph, N = group order).
Wall time = first to last activity from its NOTES, scoreboard or logs. Units: ORBW=3 energy for descents, plain
uncovered vertices for scans and RANDORB. Verdicts: lead, dead, or inconclusive.

| run | card | structure computed on | wall time | best (units) | verdict | one-line reason |
|---|---|---|---|---|---|---|
| c1-grind | F15W3 fresh-seed grinds on psl 23×Z97 (g1) and prod psl 7 sl 8 ×Z7 (g2) | psl 23×Z97: N = 588,984 (2N = 1,177,968); prod: N = 592,704 (2N = 1,185,408) | 21:45 to before 03:26 (5 h 40 min) | psl 9 (ORBW=3); prod 6 (ORBW=3, chain 352) | inconclusive (best lead for descents) | lowest tails of the squad; no chain ≤ 3, no cost 0; prod min-6 chain not yet on scoreboard |
| c2-repair | two-orbit moves from 119 good states | psl and prod groups as c1 (N 588,984 and 592,704) | 23:15 to 00:37 | 3 (ORBW=3, unchanged) | dead | no 1- or 2-move (K = 100) lowered any of 5 starts |
| c3-twist | twisted groups tpgl, csl; RANDORB; 6 descents | sl 23×Z49: N = 595,056 (2N = 1,190,112); tpgl 23×Z49 same N | 21:46 to 21:53 (stopped) | RANDORB min 47 (sl 23×Z49); chain min 18 | dead | tpgl median 345 vs 132 (RANDORB); csl with n ≡ 2 mod 4 is SL×Z_{n/2} |
| c3b-sl23x49 | descents on sl 23×Z49 (ORBW 2/3/4); RANDORB of 8 other sl(q)×Z_n | N = 595,056 (2N = 1,190,112); screens N 588,360 to 599,088 | 21:56 to 01:27 | chain min 12 (ORBW=3, 88 chains); RANDORB min 49 (sl 13×Z271) | dead | median 24 vs 21 for psl 23×Z97; other sl(q)×Z_n RANDORB medians 306 to 36,657 |
| c3c-grind | F15W3 fresh-seed grind, psl 23×Z97, seeds 108471-108480 | N = 588,984 (2N = 1,177,968) | 01:37 to 03:25 (1 h 48 min) | chain min 12 (137 chains) | inconclusive | same group as c1 g1; no chain ≤ 9 |
| c4-groups | screen of 3,850 groups; descents on psl 29×Z49 and psl 27×Z61 | screen N 588,241 to 600,000; descents on N = 596,820 and N = 599,508 | 21:45 to about 23:40 | chain min 12 (psl 29×Z49, 40 chains, median 21) | lead (weak) | psl 29×Z49 has reference median and a better screen score; sample is 40 chains |
| c5-selfdual | self-dual pairing S⁻¹ = β(S); RANDORB 3000 samples | psl 23×Z97 (N 588,984); prod psl 5×psl 27 (N 589,680) | about 21:50 to 22:15 | RANDORB min 113 plain (prod psl 5×psl 27) | dead | ι-fixed elements and the Z-part; β-2 prod run invalid |
| c5b-cosetscreen | screen of about 18 coset-graph families (40 to 1,060 samples each) | 2N = 1,185,912 to 1,200,876 | about 22:17 to 00:30 | 55 plain (family K sample, 1,060 samples) | dead | superseded by the exhaustive scans; non-regular dc 3 to 10 times worse |
| c5c-scanC | exhaustive scan of family C (PGL(2,181), D5 nonsquare) | N = 592,956 (2N = 1,185,912); 16,407 classes, 59,202 members | 00:30 to 02:13 | 44 plain (exact, family minimum) | dead (exhaustive) | no cost 0 in the family |
| c6-hexagon | annealed voltage lifts of H(q) + 2 matchings, q = 3, 4, 5 | 16,016 to 117,180 vertices (Δ 6 to 8) | 22:04 to about 00:10 | cost 0 at Δ6, Δ7, Δ8 (not target) | dead for target | valid only for Δ ≤ 8; q = 7 not reached |
| c6b-exhaust | exhaustive scan of family K (PSL(2,229), D5, one regular dc) | N = 600,438 (2N = 1,200,876); 16,293 classes, 59,985 members | 23:57 to 00:51 | 4 plain (exact, class 4233) | dead (exhaustive) | no cost 0 in K; minimum 4 pending the coordinator's check |
| c6c-h12 | coset families for h = 12 over PGL(2,193): A4, D6 nonsquare, D6 square | N = 599,072 (2N = 1,198,144); 13,797 / 27,408 / 40,480 sets | 01:01 to 02:40 | 501 (A4), 1266 (D6nsq), 900 (D6sq) plain | dead | all far worse than K (4) and C (44) |
| c7-throughput | schedule comparison (reference, COOL 7.5, COOL 30) on psl 23×Z97 | N = 588,984 (2N = 1,177,968) | 23:16 to 00:43 | chain min 3 (reference v0, energy 3); 35, 40, 19 chains | inconclusive | no schedule separates on ≤ 9 / ≤ 12 at this size |
| c7b-design | structure of annealed H(q) lifts; formula families; K-symmetric lifts | H(3), H(5), H(7) incidence graphs (39,216 vertices per H(7) copy); up to 30 copies | 00:47 to about 02:44 | cost 0 at Δ6 (30 copies) and Δ8 (20, 21 copies), not target; Δ10 best 559 (not valid) | dead for target | no valid Δ10 lift; no formula family beat random voltages |
| c8-wild | non-Haar coset graphs: PSL(2,181) C5 (two dc), PGL(2,181) D5 (one dc) | 2N = 1,185,912 | 21:59 to 22:01 (last log write) | 57 plain (PSL C5, 60 random) | dead | about 3 times worse than Haar k = 3 |
| c8b-coset | fast coset evaluator and annealer on PSL(2,181) C5 | 2N = 1,185,912 | 22:18 to 23:49 | 45 plain (9 units of 5) | dead | annealing did not beat random members; symmetric pairs min 431 |
| c8c-smooth | smooth term in k = 3 annealer; A/B (base, SMOOTHW=1, SMOOTHW=2) | psl 23×Z97 (2N = 1,177,968) | 00:08 to about 02:32 | chain min 6 (SMOOTHW=1, one chain); base 9 | inconclusive | 30 vs 29 chains; ≤ 12: 2 vs 3; no separation |
| c8d-grind | F15W3 fresh-seed grind, psl 23×Z97, seeds 108981-108990 | N = 588,984 (2N = 1,177,968) | 02:15:54 to before 03:26 (about 1 h 10 min) | chain min 12 (88 chains) | inconclusive | same group as c1; no chain ≤ 9 |
| c1b-structure | random vs biased start (C3E best of 50) on psl 23×Z97 | N = 588,984 (2N = 1,177,968) | 23:54 to 01:24 (timeout) | chain min 12 (70 chains) | inconclusive | random median 21 vs biased 18 over 35 chains each; ≤ 12: 1 vs 2 |
| c2b-digest | status digest for the coordinator (reads only; no search) | none | 00:46 to 03:30 | n/a | n/a | digest only |

## Totals: psl 23 97 and prod grinds (all CHAIN lines, F15W3, ORBW=3 unless stated)

psl 23 × Z97 (2N = 1,177,968; all runs of this group in the squad):
| source | chains | min | median | ≤ 12 | ≤ 9 |
|---|---|---|---|---|---|
| c1-grind g1 | 448 | 9 | 21 | 18 | 6 |
| c3c-grind g3 | 137 | 12 | 21 | 3 | 0 |
| c8d-grind g4 | 88 | 12 | 21 | 2 | 0 |
| c7 reference v0 | 35 | 3 | 18 | 2 | 2 |
| c7 variant v1 (COOL 7.5) | 40 | 15 | 18 | 0 | 0 |
| c7 variant v2 (COOL 30) | 19 | 9 | 18 | 2 | 1 |
| c8c base | 29 | 9 | 18 | 3 | 1 |
| c8c SMOOTHW=1 | 30 | 6 | 18 | 2 | 1 |
| c8c SMOOTHW=2 | 16 | 12 | 21 | 2 | 0 |
| c1b-structure (A/B) | 70 | 12 | 18 | 3 | 0 |
| **total psl 23 97** | **912** | **3** (c7 reference v0) | | | |
| of which the three grinds (c1 g1, c3c, c8d) | 673 | 9 | | | |

prod psl 7 × sl 8 × Z7 (2N = 1,185,408; c1-grind g2 is the only prod grind):
| source | chains | min | median | ≤ 12 | ≤ 9 | ≤ 6 |
|---|---|---|---|---|---|---|
| c1-grind g2 | 442 | 6 (chain 352) | 21 | 10 | 2 | 1 |
| **total prod** | **442** | **6** | | | | |

Notes: the c7 variants and the c8c SMOOTHW arms are counted as psl 23 97 chains; for SMOOTHW the CHAIN minimum is the true
energy (card). Counts are from the log files as they stood at 03:26 UTC.
