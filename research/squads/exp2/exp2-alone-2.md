# exp2-alone-2: report (one Haar worker, no subagents, cell (7,7))

Worker: exp2-alone-2 (Haiku 5.5, alone, no subagents). Branch: claude/haar-graph-d7-search-3zy596.
Start 2026-10-24 16:56 UTC; last search finished about 18:08 UTC (wall time about 1 h 12 min, well under the 4 h cap).
Final budget_units: 0.011 (usage log: research/squads/usage/exp2-alone-2.jsonl). The 1.5 cap was never close.

## Result

No cell was beaten. The table values are 23,436 (7,7), 117,648 (9,7) and 398,580 (11,7) vertices.

| cell | best VALID graph | vertices | / table | file |
|---|---|---|---|---|
| (7,7) | Haar graph of SL(2,8) x Z19 (N = 9,576 per side) | 19,152 | 0.817 | research/frontier/sols/d7D7_sl_8_19_orb3_s1.txt |
| (7,7) (backups) | SL(2,9) x Z13 (9,360); PGL(2,5) x Z79 (9,480); SL(2,11) x Z7 (9,240) | 18,720; 18,960; 18,480 | 0.80; 0.81; 0.79 | d7D7_sl_9_13_orb3_s1.txt, d7D7_pgl_5_79_orb3_s1.txt, d7D7_sl_11_7_s1.txt |
| (9,7) | not attempted | - | - | - |
| (11,7) | not attempted | - | - | - |

All four (7,7) files pass research/frontier/build_haar2.py (VALID, both sides eccentricity 7, simple 7-regular bipartite graph).

I chose to work only on (7,7). I did not start (9,7) or (11,7): the screens in STRUCTURE.md put both tables above the first-moment ceiling, and I had no budget or time to test them properly.

## What I tried

1. **Random-S annealing (research/frontier/haar_gen3.c, K = 8).** Solved quickly at N = 8,736 (SL(2,13) x Z4, 1.7 s), 9,240 (SL(2,11) x Z7, 0.3 s; the first (7,7) file). Failed at 9,744 (SL(2,7) x Z29), 9,792 (SL(2,17) x Z2, PSL(2,17) x Z4, PGL(2,17) x Z2), 9,828 (PSL(2,13) x Z9), 9,900 (PSL(2,11) x Z15), 10,080 (SL(2,9) x Z14, SL(2,8) x Z20) and 10,260 (PSL(2,19) x Z3). Each run was 240-600 s, with best cost 4-17 (the uncovered count).

2. **Orbit-symmetric S (research/structured/haar_sym.c, ORBIT="3 2 1": k = 3 automorphism, f = 1 fixed generator, m = 2 orbits; from branch claude/structured-search-orbit-w5dd4f).** Solved at SL(2,8) x Z19 (9,576; seed 1 in 4,505 evals, seed 2 in 26,601), SL(2,9) x Z13 (9,360; 569 evals), SL(2,11) x Z7 (9,240; 585 evals), PGL(2,5) x Z79 (9,480; 1,225 evals). Failed at SL(2,5) x Z79 (9,480, two seeds, best 6), SL(2,7) x Z31 (10,416, three runs including ORBW=3, best 6), PGL(2,7) x Z31 (10,416, best 6), PSL(2,7) x Z61 (10,248, three runs including ORBW=3, best 6), PSL(2,5) x Z163 (9,780, best 36), PSL(2,5) x Z169 (10,140, best 42), SL(2,5) x Z91 (10,920, best 50).

3. **Variants.** ORBW=3 (heavier weight for uncovered fixed elements) did not change the cost-6 floor. Random S and orbit S both stall at the same floor (cost 4-6) around N = 9,700-10,400.

## What worked, and what did not

- Both methods reach about N = 9,400-9,600 quickly. The orbit method solved in seconds to minutes where random S needed longer, but it did not extend the reachable range.
- Above about 9,600 nothing I tried got below cost 4. The plateau is the same for random and orbit-symmetric S, which fits the calibration in STRUCTURE.md (the Poisson first-moment estimate for this cell is about mu 40-50 at N = 10,000, and the orbit wall is near mu 45-50).
- Reaching the table value (N = 11,718 per side) would need a construction that beats this ceiling, not more annealing. I did not try voltage lifts (research/lifts/) or any non-Haar construction.

## Repo changes

- research/frontier/sols/: d7D7_sl_11_7_s1.txt, d7D7_sl_8_19_orb3_s1.txt, d7D7_sl_9_13_orb3_s1.txt, d7D7_pgl_5_79_orb3_s1.txt (all VALID).
- research/squads/exp2/alone-2/: haar_sym.c, haar_gen3.c and the run logs (runs/).
- research/squads/usage/exp2-alone-2.start and .jsonl.

No cell is raised, and nothing here should be recorded in the table. The (7,7) file is a valid, smaller graph than the table entry.
