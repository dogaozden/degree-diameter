# Independent re-run of research/sage (branch claude/sagemath-record-graphs-2xvt52)

Job: sage-rerun. Checker: this branch (claude/sagemath-verify-graphs-av59n3, based on the worker's commit bfc12d2).
Nothing under research/sage/ was edited. Only this file and rerun/logs/ were added.

## Environment

* SageMath: passagemath 10.8.13 (release date 2026-10-11), installed with `python3 -m venv` + `pip install passagemath-standard`
  (Python 3.13.17). The venv is outside the repo.
* Full run: `SAGE=/root/v/bin/sage ./run_all.sh` from research/sage/. All 21 steps exited 0.
* Committed logs were copied to /tmp/logs_committed before the run. After the run the fresh logs were copied to
  rerun/logs/ and research/sage/logs/ was restored with `git checkout --`, which left it unchanged.

## 1. Fresh logs against committed logs

Method: `cmp` on each of the 20 log files, fresh against committed, byte for byte. No timing lines exist in the
logs, so nothing needed to be ignored.

Result: all 20 logs are byte-identical to the committed ones. No differences.

| File | What was run | Matches committed log | Differences |
|---|---|---|---|
| d3_four_hats.sage | run_all.sh, `logs/d3_check.log` | yes | none |
| d3_16_three_gadgets.sage | run_all.sh, `logs/d3_16_check.log` | yes | none |
| d4_theoremA_ASq.sage | run_all.sh, `logs/d4_theoremA_check.log` | yes | none |
| d4_propC_Wq.sage | run_all.sh, `logs/d4_propC_check.log` | yes | none |
| d4_7_4_359_Q45.sage | run_all.sh, `logs/d4_7_4_check.log` | yes | none |
| d4 q = 7 (`sage -c`, both d4 files) | run_all.sh, `logs/d4_q7_check.log` | yes | none |
| d5_haar_7_5_1200.sage | run_all.sh, `logs/d5_haar_check.log` | yes | none |
| d5_lift_5_5_360.sage | run_all.sh, `logs/d5_lift360_check.log` | yes | none |
| d5_lift_5_5_384.sage | run_all.sh, `logs/d5_lift384_check.log` | yes | none |
| d6_theoremD_hexagon_doubling.sage | run_all.sh, `logs/d6_check.log` | yes | none |
| d6 q = 4 (`sage -c`) | run_all.sh, `logs/d6_q4_check.log` | yes | none |
| hexagon.sage | run_all.sh, `logs/hexagon_selftest.log` | yes | none |
| d7_hexagon_copies_hubs.sage | run_all.sh, `logs/d7_check.log` | yes | none |
| d8_gomez_omegaH.sage | run_all.sh, `logs/d8_check.log` | yes | none |
| compare/compare_d3.sage | run_all.sh, `logs/compare_d3.log` | yes | none |
| compare/compare_d4.sage | run_all.sh, `logs/compare_d4.log` | yes | none |
| compare/compare_d5.sage | run_all.sh, `logs/compare_d5.log` | yes | none |
| compare/compare_d6.sage | run_all.sh, `logs/compare_d6.log` | yes | none |
| compare/compare_d7.sage | run_all.sh, `logs/compare_d7.log` | yes | none |
| compare/compare_d8.sage | run_all.sh, `logs/compare_d8.log` | yes | none |

The fresh logs contain no failures. The `compare_d3.log` lines that contain "False" are parameter labels
(`filler=False`), not failed checks. The last line of each compare log is:

* compare_d3: `ALL COMPARISONS PASS`
* compare_d4: `ALL COMPARISONS PASS`
* compare_d5: `ALL COMPARISONS PASS`
* compare_d6: `ALL COMPARISONS EQUAL [('q=3', True), ('q=2', True), ('q=4', True)]`
* compare_d7: `ALL EQUAL`
* compare_d8: `ALL EQUAL`

## 2. Isomorphism check (not done by the worker)

For each record file, the graph was built by the worker's own Sage builder in this Sage, then compared with the
record's edge list using `Graph.is_isomorphic(..., certificate=True)`. Where the certificate was returned, every edge
of the Sage graph was checked to map to an edge of the record graph. Diameter and max degree come from the
Sage graphs.

| Case | Builder called | Record file | Sage graph: n, edges, max degree, diameter | Record graph: n, edges, max degree, diameter | is_isomorphic | Certificate maps every edge |
|---|---|---|---|---|---|---|
| (5,5) 360 | `build_d5_lift_5_5_360()` | research/beyond-haar-d5/records/d5D5_n360_lift_g90_6.edges | 360, 900, 5, 5 | 360, 900, 5, 5 | True | True |
| (5,5) 384 | `build_d5_lift_5_5_384('a1_g96_31')` | research/beyond-haar-d5b/records/d5D5_n384_a1_g96_31.edges | 384, 960, 5, 5 | 384, 960, 5, 5 | True | True |
| (16,3) 396 | `build_d3_16_three_gadgets()` | research/d3d6/graphs/sym3_q13_d16_n396.json | 396, 2979, 16, 3 | 396, 2979, 16, 3 | True | True |

Logs: `rerun/logs/iso_360.log`, `rerun/logs/iso_384.log`, `rerun/logs/iso_16_3.log`.

Each case ran in its own Sage process. The script is not in the repo, because the brief only allows REPORT.md and
rerun/logs/ to be written.

## Summary

* All 20 committed logs reproduce exactly.
* The three record graphs checked here (two (5,5) lifts and the (16,3) graph) are isomorphic to the Sage builder output,
  with the same vertex, edge, degree and diameter values.
* Nothing failed.

## Not checked

* The isomorphism checks compare the Sage builders with the record files. They do not check the record files against
  the (5,5)/(16,3) claims by any other route.
* No other record files were checked for isomorphism. (5,5) 384 variant `a2_g96_17` and the other families were not
  included in this job.
