# Big-record verification, job bigcheck-7c

Branch `claude/bigcheck-7c-verification-wt5tpg`. Verification only: nothing was searched, no checker code was edited, and no VALID verdict was written by hand. Each report is `research/frontier/runs/cloudcheck/<stem>.txt`: a machine line, the sha256, the full stdout of the reference checker, then the full stdout of the independent checker. Wall time and peak RSS come from `wait4` rusage and appear after each block.

Machine for every run: 4 cores, 15 GB RAM (`nproc=4`, `free -g` total 15G), kernel 6.18.44-fc-v185. Checkers built with `gcc -O3` (gcc 13.3.0).

## Results

Of the 11 files, 8 were checked, and the reference checker returned VALID for all 8. The three sl files (rows 1, 2, 5) also passed the independent checker `haarcheck2`, VALID, so they are checked by two independent checkers. The five psl files (rows 3, 4, 6, 7, 8) have no independent checker that can read them on this machine (see Method), so they are not accepted yet. Rows 9–11 were not attempted.

| # | file | vertices | cell | reference checker | ref result | ref wall / peak | independent checker | indep result | indep wall / peak | status |
|--:|---|---:|---|---|---|---|---|---|---|---|
| 1 | d9D12_sl_199_67_orb3_s1 | 1,055,973,600 | Δ9·D12 | haarcheck_sl | VALID | 320.1 s / 379 MB | haarcheck2 | VALID | 268.1 s / 253 MB | both VALID |
| 2 | d19D9_sl_131_271_orb3_s2 | 1,218,394,320 | Δ19·D9 | haarcheck_sl | VALID | 594.2 s / 437 MB | haarcheck2 | VALID | 581.2 s / 292 MB | both VALID |
| 3 | d14D10_psl_157_349_orb3_s2_n1350537864 | 1,350,537,864 | Δ14·D10 | haarcheck_psl | VALID | 847.3 s / 485 MB | none runnable | not run (~100 GB) | — | reference VALID only |
| 4 | d20D9_psl_163_421_orb3_s2 | 1,823,175,864 | Δ20·D9 | haarcheck_psl | VALID | 1498.4 s / 654 MB | none runnable | not run (~135 GB) | — | reference VALID only |
| 5 | d15D10_sl_109_991_orb5f0_s1_FIXPRE100_EARLYB1 | 2,566,531,440 | Δ15·D10 | haarcheck_sl | VALID | 1073.3 s / 919 MB | haarcheck2 | VALID | 937.4 s / 614 MB | both VALID |
| 6 | d10D12_psl_193_487_orb3_s1 | 3,500,976,768 | Δ10·D12 | haarcheck_psl | VALID | 1854.6 s / 1254 MB | none runnable | not run (~259 GB) | — | reference VALID only |
| 7 | d16D10_psl_179_821_orb5g_s41 | 4,708,566,360 | Δ16·D10 | haarcheck_psl | VALID | 3500.0 s / 1686 MB | none runnable | not run (~348 GB) | — | reference VALID only |
| 8 | d17D10_psl_313_229_orb3_s1 | 7,022,052,336 | Δ17·D10 | haarcheck_psl | VALID | 5289.6 s / 2513 MB | none runnable | not run (~520 GB) | — | reference VALID only |
| 9 | d18D10_psl_223_1063_orb3_s1 | 11,787,972,672 | Δ18·D10 | haarcheck_psl | not run | — | none runnable | not run | — | not attempted (6 h budget) |
| 10 | d19D10_sl_607_43_orb3_s1 | 19,233,722,496 | Δ19·D10 | haarcheck_sl | not run | — | haarcheck2 | not run | — | not attempted (6 h budget) |
| 11 | d20D10_psl_421_409_orb3_s1 | 30,518,778,360 | Δ20·D10 | haarcheck_psl | not run | — | none runnable | not run | — | not attempted (6 h budget) |

Peak memory is the process peak RSS from `wait4` (`ru_maxrss`). Wall time is elapsed time from launch to exit.

## Method

* Reference: `haarcheck_sl` for `sl` files and `haarcheck_psl` for `psl` files, built from `research/frontier/haarcheck_sl.c` and `research/structured/tools/haarcheck_psl.c` on master.
* Independent: `haarcheck2` (`research/frontier/haarcheck2.c`) for `sl` files. It parses only `sl` headers and is single-threaded (no OpenMP in the source), so the `-fopenmp` option was not used.
* `psl` files: `haarcheck2` rejects the header (`typ != "sl"`). `check_haar_indep.py` supports `psl` but uses about 74 bytes per vertex (estimated size = vertices × 74). For every psl file here that is far above 15 GB, so no second checker fits. Those reports record this as "NOT RUN" with the estimate, and the file is not accepted.
* Files checked one at a time. Each sol file was copied from its branch with `git show` and committed before its checks ran.
* No check hit the 3-hour per-check cap.

## Notes

* Row 5: the first independent attempt was killed when a background command reached its 30-minute cap, and the checker was lost with it. The reference result was kept. The independent check was rerun detached and completed with VALID. Its report reflects the rerun only.
* A first draft of the psl "NOT RUN" text had a field-index bug (it printed 0 vertices). It was corrected in the report of row 3 and in the script before rows 4–8 ran. Rows 4–8 show the right vertex counts.
* Rows 9–11 were not started because the reference alone for row 9 (about 12 billion vertices, 18 generators) would run past the remaining budget. Row 10 (sl, 19 generators, 19 billion vertices) and row 11 (psl, 20 generators, 30 billion vertices) would hit the 3-hour cap.

## Watch

* Two independent checkers were used only for sl files. For psl files there is no second checker on this machine, so the reference result alone does not accept those files.
* Independence caveat: `haarcheck_sl` and `haarcheck2` both read the same solution-file format and conventions. A shared misreading of a convention would not be caught by running both.
* One machine: 4 cores, 15 GB RAM.
