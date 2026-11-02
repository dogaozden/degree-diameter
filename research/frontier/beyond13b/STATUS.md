# beyond-d13b status (stopped 2026-11-02 01:10 UTC on Doğa's budget stop)

Checked raises of the D = 13 column (rows spliced into research/frontier/beyond/BEYOND_TABLE.md):

| cell | was | now | group | check |
|---|---:|---:|---|---|
| (5,13) | 3,594,910 | 3,729,966 | Z32719 x\|_29509 Z57 | metacheck + build_haar2 VALID |
| (6,13) | 41,734,392 | 43,702,560 | SL(2,89) x Z31 | haarcheck_gen VALID |
| (7,13) | 312,227,760 | 320,463,216 | SL(2,163) x Z37 | haarcheck_gen VALID |
| (8,13) | 1,739,514,000 | 1,758,180,960 | SL(2,359) x Z19 | haarcheck_gen VALID |
| (9,13) | 7,924,036,032 | 8,067,489,456 | SL(2,677) x Z13 | haarcheck_gen VALID |

Candidate, not yet a table row: (10,13) 29,088,880,800 (+45.6 %), Haar graph SL(2,601) x Z67, S = e + 3 alpha-orbits,
search cost 0 (17 evaluations). haarcheck_gen's (e,A) BFS passed (every element of both sides within 13); the (e,B) BFS
was stopped unfinished. Solution: research/frontier/sols/d10D13_sl_601_67_orb3-3-1_s1_candidate.txt; partial log:
research/frontier/beyond13b/runs/d10D13_sl_601_67_orb3-3-1_s1.gen.partial.txt. Needs the full check (about 1-1.5 h on
4 threads, 10.6 GB; or haarcheck_sl in two halves).

Left undone: see the last paragraph of SECTION_D13B.md (near misses with saved states under research/squads/beyond13b/,
round-3 plan with a higher final annealing temperature, SL(2,607) x Z67 for (10,13), SL(2,599) x Z19 for (9,13)).
