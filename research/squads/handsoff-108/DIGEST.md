# handsoff-108 digest (c2b-digest)

Last rewrite: 2026-11-01 01:10 UTC. Next rewrite about 01:35 UTC. Target cell: Δ10, D8, more than 1,176,480 vertices
(Haar: N ≥ 588,241, |S| = 10). Numbers are copied from NOTES.md, scoreboard.tsv and log tails; units are as stated.

**CLAIMS OF COST 0 FOR THE TARGET CELL: NONE.** Two kinds of cost-0 numbers exist, and neither is in the target cell:
- scoreboard, c6-hexagon (voltage lifts of H(q) plus two matchings, Δ = q+3): 16,016 (Z22, H(3), Δ6), 17,472 (Z24, H(3), Δ6),
  54,600 (Z20, H(4), Δ7), 109,368 (Z14, H(5), Δ8), 117,180 (Z15, H(5), Δ8).
- c7b-design/runs/hz_summary_q3.txt (NOT on the scoreboard): "cost 0" at q = 3 (Δ6) for m = 12, 16, 20, 24 (8,736 to 17,472
  vertices), matching-only runs with hexagon voltages 0. m = 28 gives cost 28.
The best cost in the target-type families so far is 4 plain (family K, exhaustive, see row c6b). Nothing is a record.

**Flags for the coordinator (found while digesting):**
1. RESOLVED. The earlier worry about c6b-exhaust/run_all.sh starting a second family-C scan is gone: c6b's NOTES say the
   wrapper was stopped before its C step, and no c6b process is alive.
2. c3b-sl23x49: screen.sh waits for driver.done, which driver.sh never wrote (its three descents ended about 23:42 UTC).
   The RANDORB screens of sl 13 271, sl 9 823, ... have never started. c3b's NOTES results section is still empty.
3. c5c-scanC: the last scoreboard line for it (530, 00:42) is stale. Its own tables already give an exact C of 405.
4. c1-grind: g1 has three chains at minimum 9 (CHAIN 163, 211 and 250 in g1.log). The scoreboard rule is ≤ 6, so
   nothing was written. Not a claim.
5. c6c-h12 is a worker folder that is not on the card list (see its row). It has no NOTES.md yet.

## Status and key numbers

Units: ORBW=3 energy for every F15W3 descent (chain minimum = CHAIN field 4) unless stated. "plain" = uncovered vertices.
Reference for F15W3 on psl 23 × Z97 (c1 logs, same schedule): chain median 21, chains ≤ 9 about 1 in 15 (card).

| worker | card | status (01:09 UTC) | key numbers | main finding | cost-0 claim? |
|---|---|---|---|---|---|
| c1-grind | volume on psl 23 97 and prod psl 7 sl 8 7 | running: g1 pid 2553 and g2 pid 3125, about 56 % CPU each; budget ends about 04:25 UTC | g1: 269 chains, min 9, median 21, ≤12: 11, ≤9: 3. g2: 269 chains, min 12, median 21, ≤12: 6, ≤9: 0. Scoreboard: 15 (21:50), 12 (22:45) | Best tail so far: 3 chains at 9 and 17 at ≤12 in 538 descents; no cost 0 | no |
| c1b-structure | what makes a good orbit set (random vs biased start A/B) | running: pid 15350, timeout ends about 01:24 | 57 chains: min 12, median 18, ≤12: 3. Random-start arm 28 chains (median 21, one ≤ 12); biased-start arm 28 chains (median 18, two ≤ 12) | No separation between arms yet; c1b NOTES: 84-95 % of chain ends already reach c3 = 0, so that statistic is not a start signal | no |
| c2-repair | two-orbit moves from the 119 good states | done (no processes) | 5 starts: 2 at energy 3 (psl), 3 at energy 6 (2 prod, 1 psl). K = 100; about 3 × 10^4 pair evaluations per state (c2 NOTES summary 00:37) | No 1-move or 2-move (K = 100) improvement for any start | no |
| c3-twist | twisted cyclic factor (tpgl, csl) | stopped early at 21:53 (no processes) | RANDORB: tpgl 23×Z49 median 345 vs sl 23×Z49 median 132. sl 23×Z49 F15W3: 6 chains, minima 18, 18, 24, 24, 27, 27 | tpgl is worse; csl with n ≡ 2 mod 4 is just SL(2,q)×Z_{n/2} | no |
| c3b-sl23x49 | descents on sl 23 × Z49 and ORBW tests | descents done; RANDORB screen STALLED (flag 2); no processes | d1 (ORBW=3, 4000 s): 88 chains, min 12, median 24, ≤12: 1, ≤9: 0. d2 (ORBW=2, 1200 s): 26 chains, min 17, median 23 (ORBW=2 units). d3 (ORBW=4, 1200 s): 24 chains, min 18, median 24 (ORBW=4 units) | sl 23×Z49 descents are not better than psl 23×Z97 (median 24 vs 21 at ORBW=3) | no |
| c4-groups | screen of direct-product groups | done (descents.done; no processes) | 3850 candidate groups; 300-sample screen of 473 non-meta groups with n ≤ 5000. Top by (p1+p10)/2/μ: prod psl 7 pgl 8 ×Z7 (0.917), prod psl 7 sl 8 ×Z7 (0.932, grind group), psl 29 ×Z49 (0.959), sl 23 ×Z49 (0.959), psl 27 ×Z61 (1.035), psl 23 ×Z97 reference (1.048). Descents: psl 29×Z49 (d1): 40 chains, min 12, median 21, ≤12: 1. psl 27×Z61 (d2): 39 chains, min 21, median 27 | psl 29×Z49 matches the reference median and has a better screen score; psl 27×Z61 is worse; n > 5000 and meta groups are out (pilot medians 92k to 520k, meta n = 1: 3.4k to 569k) | no |
| c5-selfdual | twisted self-dual pairing S⁻¹ = β(S) | done (dead; no processes) | RANDORB min of 3000 (plain): psl 23×Z97 with inner β 125,257 (median 141,318); prod psl 5 × psl 27 with β inverting α 113 (median 1226). The β-2 prod run is invalid (β does not normalise α) | Dead: the ι-fixed elements and the Z-part kill the family | no |
| c5b-cosetscreen | screen of coset-graph families | done (no processes) | 14 round-1 families plus four extras (K2, C2, A2, K3). Family K = PSL(2,229), D5, one regular double coset: sample min 87, median 340 (n = 60); best sampled member full C = 55 plain (rep key 134144, 1,060 samples). Family C = PGL(2,181), D5 nonsquare: min 127, median 456 (n = 100). h = 6 families: min 101 to 1920 | Non-regular double cosets 3 to 10 times worse; square-reflection D5 and C10 in PGL(2,181) are disconnected | no |
| c5c-scanC | full scan of coset family C (16,407 classes) | running scanA: pid 22618, timeout 7800 s from 00:30 (ends about 02:40); 12,376 of 16,407 classes at 01:09 (about 340 per minute) | Exact full C over 1,056 self-inverse classes (2,069 members): best 405. Lower bound P = uBA+uAA over scanned classes: min 44 (not exact). scanB (B-root) not started | No family C class below 405 so far | no |
| c6-hexagon | structured lifts of H(q) | done (no processes) | Valid lifts (Δ < 10 only): q=3 Z22 (16,016), q=3 Z24 (17,472), q=4 Z20 (54,600), q=5 Z14 (109,368), q=5 Z15 (117,180). q=5 Z16 not reached. q=7 evaluation about 1 min | Annealed lifts work for q ≤ 5 only; nothing at Δ10 | no for the target cell (see top) |
| c6b-exhaust | exhaustive scan of coset family K (PSL(2,229), D5, one regular double coset) | done: all 16,293 classes (59,985 members); no processes | Exact best C = 4 plain (class 4233; uBA 4, uAA 0, uBB 0). Exact top 10: 4, 33, 37, 41, 42, 45, 45, 46, 47, 50 (c6b NOTES). Scoreboard line 00:51 (cost 4, plain, "not diameter 8"). Not yet checked independently by the coordinator | Family K has no cost 0; its minimum is 4 plain (not 0) | no |
| c6c-h12 | NOT on the card list: scans of h = 12 coset families over q = 193 | running A4 scanA (timeout pid 10064, 3000 s from 01:04); 1,042 classes at 01:09; next D6nsq scanA. No NOTES.md yet | none on the scoreboard yet | New family scan; the names of its outputs suggest A4 and nonsquare D6 subgroups, and the c5b card sizes suggest N = 599,072 (2N = 1,198,144) | no |
| c7-throughput | more good descents per CPU-hour | stopped (checked 00:43; no processes) | Chains ≤ 12 per arm: v0 (reference) 2/35; v1 (COOL 7.5) 0/40; v2 (COOL 30) 2/19; grind 5/245 (wall clock). Chain minima: v0 3, v1 15, v2 9 | No schedule separates on the ≤ 9 / ≤ 12 tail at this sample size; COOL 7.5 and 30 give about 1.5 to 1.8 times more chains at ≤ 15 per CPU-hour | no |
| c7b-design | structure in the annealed hexagon lifts | done (NOTES.md, 117 lines); bottom line negative: no formula family beat random voltages; no processes at 01:08 | Matching-only runs (hexagon voltages 0), q = 3: cost 0 at m = 12, 16, 20, 24; cost 28 at m = 28; 322 at m = 32 (runs/hz_summary_q3.txt). c7b: at Δ10 with m ≥ 29, random lifts are not expected | Negative: the valid lifts look like random ones; the table's 30 copies at q = 7 would need structure, not luck. Flag 5 is the cost-0 lines at Δ6 | no for the target cell (see top) |
| c8-wild | coset graphs (Haar alternative) | done (no processes) | PGL(2,181) D5, one double coset: min 150 (40 candidates). PSL(2,181) C5, two double cosets: best 57 plain (60 random) | Coset graphs look about 3 times worse than Haar k = 3 descents (c8c notes) | no |
| c8b-coset | fast coset evaluator and annealer (PSL(2,181), C5) | done (processes stopped) | Best 45 plain (9 units of 5), 21 chains, median chain minimum about 57 plain. Scoreboard lines 76 and 39 were invalid (corrected to 166). Symmetric pairs: min 431 (6,164 pairs) | No cost 0; coset annealing does not beat Haar | no |
| c8c-smooth | smoother objective for the k = 3 annealer | running: smooth arm (SMOOTHW=1, pid 29167) from 00:54, timeout 5400 s; then ab_extra.sh (SMOOTHW=2, 3000 s) queued | Base arm (ORBW=3): 29 chains, min 9, median 18, ≤12: 3, ≤9: 1. Smooth arm so far: 12 chains, min 6 (one chain, true energy), median 18, ≤12: 2, ≤9: 1. Scoreboard line 01:04 (cost 6) | Too early: one chain at 6 is not significant; the smooth arm needs its full sample | no |

## Leads worth more CPU

1. psl 23 × Z97 F15W3 (c1-grind, both grind runs). Still the lowest tail: 3 chains at 9 and 17 at ≤ 12 in 538 descents
   (g1.log lines 576, 744, 883 for the 9s). Keep it running; seeds used are 108101 and 108201 (card range 108101-108299).
2. Family K member class 4233 (C = 4 plain, c6b NOTES): the exhaustive minimum of family K, uBA 4, uAA 0, uBB 0. Not a cost 0
   and not diameter 8. Nothing has yet been run from it (no local search). The coordinator's independent check is pending.
   Haar energy-3 states use ORBW=3 units, so the two numbers are not directly comparable.
3. psl 29 × Z49 (c4-groups d1.log): RANDORB score 0.959 against 1.048 for the reference (c4 NOTES table, ranks 3 and 7).
   Descents so far: 40 chains, median 21, min 12 (one chain ≤ 12). Same median as the reference on a different group, with the
   best screen score among the non-grind groups that were descended. Sample is small.
4. c6c-h12 (h = 12 families, new at 01:04): a different family from the C scan, with N = 599,072 (2N = 1,198,144) if the
   inferred group is right. Its A4 pass runs first.
5. c5c family C: the A-root pass should finish in about 12 minutes at the current rate (4,031 classes left at 01:09); then scanB
   for classes with P ≤ 50.
6. c8c smooth objective: waiting for the smooth-arm sample (12 chains so far).

## Dead ends

- c2-repair: no 1-move or 2-move (K = 100) from the 5 good states lowered the energy (c2-repair/NOTES.md, summary 00:37).
- c3-twist: tpgl twists are worse (RANDORB median 345 vs 132 for sl 23×Z49, c3-twist/NOTES.md).
- c3b-sl23x49: descents not better than psl 23×Z97 (median 24 vs 21, 88 chains at ORBW=3).
- c4-groups: groups with n > 5000 (pilot medians 92k to 520k) and meta groups (n = 1 pilots median 3.4k to 569k).
  psl 27 × Z61 descents: median 27 (39 chains).
- c5-selfdual: iota-pairing family (scoreboard 22:11): psl 23×Z97 min 125,257 plain; prod psl 5 × psl 27 min 113 plain,
  median 1226 (3000 samples each).
- c5b-cosetscreen: h = 6 families (PSL(2,193) C6 and S3, PGL(2,193) D6): sample minima 101 to 1920 plain; non-regular
  double cosets 3 to 10 times worse.
- c6b-exhaust: family K exhausted: no cost 0 among 59,985 members (minimum 4 plain).
- c6-hexagon: annealed lifts at q = 7 hopeless (one evaluation about 1 min); lifts at q ≤ 5 do not reach Δ10.
- c7b-design: no formula family beat random voltages; annealing or random sampling at Δ10 for m ≥ 29 is not worth the CPU
  (c7b NOTES, section 5).
- c7-throughput: no schedule separates on the tail (0 to 2 per arm).
- c8-wild / c8b-coset: coset annealing best 45 plain (9 units of 5), median chain minimum about 57 plain.
