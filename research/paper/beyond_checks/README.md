# Second checks run by job paper-beyond (2026-11-01)

Rows of the BEYOND.md table that had only one checker (or only the finder's own check) were re-checked here with a
checker written separately from the one already used. Each log starts with the file and its sha256, and the checker.

- Haar graphs of SL(2,p) x Z_n / PSL(2,p) x Z_n from branch claude/beyond-d13-search-z35z61 (research/frontier/sols/):
  `research/frontier/haarcheck_sl.c` / `research/structured/tools/haarcheck_psl.c` from master 9a97f7a5 (gcc -O3,
  single-threaded). The search session had checked them with haarcheck_gen. `*.ref.txt` = both BFS in one run;
  `*.refA.txt` / `*.refB.txt` = BFS from (e,A) / (e,B) in two runs (both halves are needed).
- Metacyclic Haar graphs: `research/frontier/build_haar2.py` (master) on the two D = 13, 14 files the search session
  had checked with its own metacheck/metacheck2; `research/frontier/beyond13/metacheck.py` (branch
  claude/beyond-d13-search-z35z61) on master's (4,11), (5,11), (5,12) and (6,11) files, whose master logs have
  build_haar2.py only (the all-pairs logs of (4,11) and (5,11) are on branch claude/beyond-d11-d12-new-cells-3t3djx).
- Edge lists: `research/lifts/coordinator_check/apsp.c` (all pairs, no symmetry), also at D - 1, where it must fail.
  (3,11) 1,474 from branch claude/new-cells-beyond-etos3t (research/frontier/beyond/graphs/), (17,5) 35,728 from branch
  claude/beyond-small-cells-fwb6si (research/squads/beyond-small/graphs/).

The solution files and edge lists were taken unchanged from those branches (git show); the sha256 in each log
identifies them.

## Results

| cell | file | checker | result |
|---|---|---|---|
| (6,13) | d6D13_psl_83_73_orb3-2-0_f11 | haarcheck_psl | VALID |
| (7,13) | d7D13_sl_229_13_orb3-2-1_e10 | haarcheck_sl | VALID |
| (8,13) | d8D13_sl_499_7_orb3-2-2_s2 | haarcheck_sl | VALID |
| (9,13) | d9D13_sl_593_19_orb3-3-0_s6 | haarcheck_sl, A and B halves | HALF-VALID + HALF-VALID = VALID (21 min per half) |
| (6,14) | d6D14_sl_97_103_orb3-2-0_g07 | haarcheck_sl | VALID |
| (7,14) | d7D14_psl_223_151_orb3-2-1_h14 | haarcheck_psl | VALID |
| (8,14) | d8D14_psl_397_181_orb3-2-2_s4 | haarcheck_psl, A and B halves | HALF-VALID + HALF-VALID = VALID (40 min per half; a first A run was killed for memory and rerun) |
| (5,13) | d5D13_prodmeta_11_5_2971_11_i06 | build_haar2.py | VALID |
| (5,14) | d5D14_meta_148781_43_i07 | build_haar2.py | VALID |
| (5,12) | d5D12_meta_8969_59_205_b6l03 (master) | metacheck.py | VALID |
| (6,11) | d6D11_meta_20809_51_12972_b5k07 (master) | metacheck.py | VALID |
| (4,11) | d4D11_meta_523_29_9_b2h01 (master) | metacheck.py | VALID |
| (5,11) | d5D11_meta_5023_31_2886_b5k05 (master) | metacheck.py | VALID |
| (3,11) | d3D11_n1474_meta67_11_9.edges | apsp.c | VALID at D = 11, INVALID at D = 10 |
| (17,5) | d17D5_n35728_orbits.edges | apsp.c | VALID at D = 5, INVALID at D = 4 |

Not completed: the reference check of (10,13) (d10D13_psl_503_157_orb3-3-1_s1, about 7 GB per half). The A half was
killed by the session's memory limit after 20 minutes when the B half was started beside it, and the B half was then
stopped, since running the halves one after the other would have taken about two more hours. (16,11) was not
attempted.
