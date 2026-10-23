# Big-record verification: independent low-memory checker (`bigcheck_indep`)

Branch `claude/bigcheck-indep-haar-cdziu4`. Nothing was searched; this is verification only.

## Result

**All 69 Haar-graph files with more than 2,000,000 vertices on `claude/structured-haar-search-ws7bet` are VALID under both checkers** (the repo's reference checker and the new `bigcheck_indep`), including the four pending finds:

| pending find | vertices | reference checker | `bigcheck_indep` |
|---|---:|---|---|
| `d10D10_sl_79_61_orb3_s1` | 60,141,120 | `haarcheck_sl` VALID | VALID, eccA=eccB=10 |
| `d13D9_sl_101_31_orb3_s1` | 63,872,400 | `haarcheck_sl` VALID | VALID, eccA=eccB=9 |
| `d14D9_sl_67_193_orb3_s1` | 116,068,656 | `haarcheck_sl` VALID | VALID, eccA=eccB=9 |
| `d16D9_sl_149_49_orb3_s1` | 324,164,400 | `haarcheck_sl` VALID | VALID, eccA=eccB=9 |

Each has a report in `research/frontier/runs/cloudcheck/<stem>.txt` (machine line first, then the full stdout of both checkers, copied verbatim by the shell, nothing hand-edited). The largest, `d14D10_sl_443_7_s1` (1,217,130,096 vertices), took 393 s and 292 MB with `bigcheck_indep` (reference: 475 s, 437 MB).

## The checker

`research/frontier/bigcheck_indep.c`, written from scratch (none of `haarcheck_sl.c`, `haarcheck_psl.c`, `haarcheck2.c`, `haar_gen3.c`, `haar_sym.c` was read while writing it). Build: `gcc -O2 -fopenmp -o bigcheck_indep bigcheck_indep.c`.

* Own closed-form element numbering (no tables, no sorting): SL by (a,b,c) or (b,d); PSL by choosing the representative of {x,-x} for a (or b); PGL by scaling the first nonzero of (a,b) to 1. G index = rank*NCYC + z; `prod` of two factors supported.
* Supports `sl`, `psl`, `pgl` over prime fields and over GF(p^k) (table arithmetic, polynomial from the file, irreducibility and field axioms checked), `prod` of two such factors, times Z_n. Anything else (meta, agl1, cyc, csl, tpgl, nested prod) prints `RESULT UNSUPPORTED <reason>`.
* BFS keeps 4 bitsets over G (visited A, visited B, frontier, next): N/2 bytes total, multi-threaded with OpenMP.
* Checks: d distinct elements of S, all in the group; numbering proven bijective on every start-up (rank(unrank(i))=i for all i, determinants, class invariance, associativity on random triples); s·s⁻¹ = e; every vertex of both sides has d distinct, in-range neighbours (exhaustive, all N per side); adjacency symmetry; BFS from (e,A) and (e,B) reaches 2|G| vertices; both eccentricities <= D (`--D n` overrides D). Prints the level sizes and the final line `RESULT VALID d= D= eccA= eccB= n=` only if everything passes, else `RESULT INVALID <reason>`.

## Validation (`research/frontier/runs/bigcheck_indep_validation.txt`, unedited script output)

* (a) Level sizes from both sources agree **exactly** with `check_haar_indep.py` on 13 records on master: sl, psl, pgl, GF(p^k) (27, 81), prod (incl. GF(8)xGF(8)), vertex counts 0.45M-16.8M, several n.
* (b) One element of S changed: 5 shear variants (sl, psl, pgl, various generators) all give INVALID (eccentricity grows by 1 or 2, matching `check_haar_indep.py` on the two I cross-ran); a duplicated generator and an out-of-group matrix are INVALID; a hand-made disconnected case (3 unitriangular generators) is INVALID with "reaches only 38 of 13680", also matching the Python checker.
* (c) D lowered by 1 on 7 tight records (sl, psl, pgl, prod, up to 8M): INVALID every time ("ecc from A is D > D-1").
* An unsupported family (meta) is rejected with `RESULT UNSUPPORTED`.

## Scope decisions (please check)

* "Newer files above 2,000,000 vertices with no cloudcheck report": no `cloudcheck/` report existed on any `claude/*` branch, and the structured branch had no sol file newer than the four listed (125 files, head `1421b53` at the end), so I checked **every** file above 2M vertices (65 besides the four). Reports are pushed one commit per file.
* `haarcheck_sl` only reads `sl p` with p prime, `haarcheck_psl` only `psl p`. For the 27 GF(p^k) / pgl / prod files the reference column is `research/frontier/build_haar2.py` instead (all of these are <= 21.4M vertices, so its memory need is fine; the 21M prod file used 2.3 GB).
* The reference checkers were compiled from the structured branch's copies and not committed. The shell wrapper only appended machine/provenance lines (including the sha256 of every sol file) around the checkers' own output.

## Caveats

* Independence is of code, not of the problem statement: both checkers read the same file format and the same conventions (matrix [[a,b],[c,d]], field element = base-p digits, edges g~s·g). The Python checker, written separately from the same file format, agrees on level sizes, which rules out an indexing or arithmetic bug in mine, but a shared misreading of a file convention would not be caught. The reported graphs' diameters are the ones implied by these conventions.
* Only one machine (4 cores, 15 GB); timings in the table are from sequential runs on it.
* The per-level progress lines (stderr) are not in the reports; stdout, which contains the level sizes and RESULT line, is complete.

## All reports

| vertices | file | reference checker | ref verdict | bigcheck_indep | ref wall s | bigcheck wall s | ref RSS MB | bigcheck RSS MB |
|---:|---|---|---|---|---:|---:|---:|---:|
| 2,104,872 | d7D10_psl_67_7_s101 | haarcheck_psl | VALID | VALID | 1 | 0 | 11 | 11 |
| 2,116,800 | d7D10_sl_49_9_s101 | build_haar2 | VALID | VALID | 6 | 0 | 327 | 11 |
| 2,125,440 | d7D10_sl_81_2_s601 | build_haar2 | VALID | VALID | 10 | 0 | 371 | 11 |
| 2,147,040 | d7D10_sl_71_3_s602 | haarcheck_sl | VALID | VALID | 1 | 0 | 11 | 11 |
| 2,234,400 | d7D10_psl_49_19_orb3_s1 | build_haar2 | VALID | VALID | 5 | 0 | 313 | 11 |
| 3,006,960 | d9D9_sl_67_5_s111 | haarcheck_sl | VALID | VALID | 1 | 0 | 11 | 11 |
| 3,019,632 | d9D9_sl_43_19_s111 | haarcheck_sl | VALID | VALID | 1 | 1 | 11 | 11 |
| 3,057,600 | d9D9_sl_49_13_s111 | build_haar2 | VALID | VALID | 9 | 1 | 418 | 11 |
| 3,104,640 | d9D9_prod_psl_11_sl_7_7_s111 | build_haar2 | VALID | VALID | 10 | 1 | 394 | 11 |
| 3,104,640 | d9D9_prod_psl_7_sl_11_7_s111 | build_haar2 | VALID | VALID | 10 | 1 | 404 | 11 |
| 3,110,400 | d9D9_prod_sl_9_sl_9_3_s111 | build_haar2 | VALID | VALID | 12 | 1 | 409 | 11 |
| 3,111,552 | d9D9_sl_73_4_s111 | haarcheck_sl | VALID | VALID | 1 | 1 | 11 | 11 |
| 3,113,280 | d9D9_sl_47_15_s111 | haarcheck_sl | VALID | VALID | 1 | 1 | 11 | 11 |
| 3,144,960 | d9D9_prod_psl_7_sl_9_13_s111 | build_haar2 | VALID | VALID | 8 | 1 | 408 | 11 |
| 3,144,960 | d9D9_prod_sl_9_sl_13_1_s111 | build_haar2 | VALID | VALID | 27 | 1 | 500 | 11 |
| 3,188,160 | d9D9_sl_81_3_s111 | build_haar2 | VALID | VALID | 13 | 1 | 453 | 11 |
| 3,290,112 | d9D9_prod_sl_7_sl_17_1_s302 | build_haar2 | VALID | VALID | 29 | 1 | 514 | 11 |
| 6,073,920 | d13D8_prod_psl_5_sl_37_1_s101 | build_haar2 | VALID | VALID | 96 | 2 | 963 | 11 |
| 6,098,400 | d13D8_prod_psl_11_psl_11_7_s101 | build_haar2 | VALID | VALID | 30 | 3 | 688 | 11 |
| 6,177,600 | d13D8_prod_psl_9_psl_11_13_s101 | build_haar2 | VALID | VALID | 24 | 2 | 671 | 11 |
| 6,209,280 | d13D8_prod_sl_7_sl_11_7_s101 | build_haar2 | VALID | VALID | 26 | 2 | 692 | 11 |
| 6,223,104 | d13D8_sl_73_8_s301 | haarcheck_sl | VALID | VALID | 2 | 1 | 11 | 11 |
| 6,408,480 | d13D8_psl_79_13_s404 | haarcheck_psl | VALID | VALID | 3 | 1 | 11 | 11 |
| 6,434,112 | d13D8_sl_47_31_orb3_s1 | haarcheck_sl | VALID | VALID | 2 | 1 | 11 | 11 |
| 6,604,416 | d13D8_prod_sl_8_sl_8_13_orb3_s1 | build_haar2 | VALID | VALID | 25 | 2 | 874 | 11 |
| 7,151,760 | d8D10_pgl_43_45_s111 | build_haar2 | VALID | VALID | 17 | 1 | 549 | 11 |
| 7,207,200 | d8D10_prod_psl_11_psl_13_5_s111 | build_haar2 | VALID | VALID | 21 | 1 | 576 | 11 |
| 7,286,400 | d8D10_prod_psl_23_sl_5_5_s111 | build_haar2 | VALID | VALID | 24 | 2 | 711 | 11 |
| 7,349,616 | d8D10_sl_107_3_s111 | haarcheck_sl | VALID | VALID | 2 | 1 | 11 | 11 |
| 7,387,200 | d10D9_prod_psl_19_sl_5_9_s111 | build_haar2 | VALID | VALID | 24 | 2 | 793 | 11 |
| 7,432,152 | d8D10_psl_83_13_orb3_s1 | haarcheck_psl | VALID | VALID | 3 | 1 | 11 | 11 |
| 7,439,040 | d10D9_sl_81_7_s111 | build_haar2 | VALID | VALID | 24 | 2 | 680 | 11 |
| 7,488,000 | d10D9_prod_psl_5_sl_25_4_s111 | build_haar2 | VALID | VALID | 28 | 2 | 710 | 11 |
| 7,596,840 | d10D9_psl_59_37_orb3_s1 | haarcheck_psl | VALID | VALID | 3 | 1 | 11 | 11 |
| 7,596,840 | d8D10_psl_59_37_orb3_s1 | haarcheck_psl | VALID | VALID | 3 | 1 | 11 | 11 |
| 7,802,160 | d10D9_sl_59_19_orb3_s1 | haarcheck_sl | VALID | VALID | 2 | 1 | 11 | 11 |
| 7,802,160 | d8D10_sl_59_19_orb3_s1 | haarcheck_sl | VALID | VALID | 2 | 1 | 11 | 11 |
| 8,003,856 | d10D9_sl_83_7_orb3_s1 | haarcheck_sl | VALID | VALID | 2 | 1 | 11 | 11 |
| 15,290,352 | d11D9_sl_197_1_s111 | haarcheck_sl | VALID | VALID | 5 | 3 | 11 | 11 |
| 15,624,000 | d11D9_sl_125_4_s111 | build_haar2 | VALID | VALID | 81 | 3 | 1298 | 11 |
| 15,940,800 | d11D9_sl_81_15_s111 | build_haar2 | VALID | VALID | 57 | 3 | 1096 | 11 |
| 16,369,920 | d11D9_prod_sl_7_sl_29_1_s111 | build_haar2 | VALID | VALID | 223 | 4 | 1909 | 11 |
| 16,483,200 | d15D8_sl_101_8_s2 | haarcheck_sl | VALID | VALID | 6 | 3 | 11 | 11 |
| 16,565,160 | d11D9_psl_61_73_orb3_s1 | haarcheck_psl | VALID | VALID | 8 | 2 | 11 | 11 |
| 16,792,080 | d11D9_sl_61_37_orb3_s1 | haarcheck_sl | VALID | VALID | 5 | 2 | 11 | 11 |
| 20,191,680 | d9D10_sl_81_19_s111 | build_haar2 | VALID | VALID | 59 | 3 | 1164 | 11 |
| 21,253,656 | d9D10_psl_277_1_s111 | haarcheck_psl | VALID | VALID | 10 | 5 | 11 | 11 |
| 21,385,728 | d9D10_prod_sl_13_sl_17_1_s111 | build_haar2 | VALID | VALID | 238 | 5 | 2323 | 11 |
| 22,178,688 | d9D10_sl_223_1_s111 | haarcheck_sl | VALID | VALID | 7 | 4 | 11 | 11 |
| 32,772,096 | d12D9_sl_127_8_s2 | haarcheck_sl | VALID | VALID | 12 | 6 | 13 | 11 |
| 57,868,272 | d10D10_sl_307_1_s3 | haarcheck_sl | VALID | VALID | 18 | 11 | 22 | 16 |
| 58,863,480 | d10D10_psl_389_1_orb3_s1 | haarcheck_psl | VALID | VALID | 28 | 15 | 23 | 16 |
| 60,141,120 | d10D10_sl_79_61_orb3_s1 | haarcheck_sl | VALID | VALID | 18 | 7 | 23 | 16 |
| 62,156,160 | d13D9_sl_109_24_s2 | haarcheck_sl | VALID | VALID | 23 | 11 | 24 | 17 |
| 63,872,400 | d13D9_sl_101_31_orb3_s1 | haarcheck_sl | VALID | VALID | 23 | 10 | 24 | 17 |
| 111,482,880 | d14D9_sl_191_8_s1 | haarcheck_sl | VALID | VALID | 43 | 21 | 42 | 29 |
| 112,363,008 | d14D9_sl_383_1_orb3_s1 | haarcheck_sl | VALID | VALID | 44 | 30 | 42 | 29 |
| 113,979,936 | d14D9_psl_113_79_orb3_s1 | haarcheck_psl | VALID | VALID | 67 | 22 | 42 | 29 |
| 116,068,656 | d14D9_sl_67_193_orb3_s1 | haarcheck_sl | VALID | VALID | 43 | 19 | 43 | 30 |
| 190,887,072 | d15D9_sl_457_1_s2 | haarcheck_sl | VALID | VALID | 79 | 65 | 70 | 48 |
| 300,799,200 | d12D10_sl_311_5_s1 | haarcheck_sl | VALID | VALID | 107 | 74 | 109 | 74 |
| 306,179,328 | d12D10_sl_337_4_s2 | haarcheck_sl | VALID | VALID | 110 | 76 | 111 | 75 |
| 310,628,640 | d12D10_sl_281_7_s3 | haarcheck_sl | VALID | VALID | 109 | 69 | 113 | 76 |
| 316,679,760 | d16D9_sl_541_1_s1 | haarcheck_sl | VALID | VALID | 135 | 186 | 115 | 78 |
| 317,308,656 | d16D9_sl_283_7_orb3_s1 | haarcheck_sl | VALID | VALID | 132 | 88 | 115 | 78 |
| 324,164,400 | d16D9_sl_149_49_orb3_s1 | haarcheck_sl | VALID | VALID | 135 | 67 | 118 | 79 |
| 622,736,928 | d13D10_sl_373_6_s1 | haarcheck_sl | VALID | VALID | 229 | 178 | 224 | 151 |
| 636,550,992 | d13D10_sl_307_11_s2 | haarcheck_sl | VALID | VALID | 234 | 152 | 229 | 154 |
| 1,217,130,096 | d14D10_sl_443_7_s1 | haarcheck_sl | VALID | VALID | 475 | 393 | 437 | 292 |

69 reports; 69 with both VALID
