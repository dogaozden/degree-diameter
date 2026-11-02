# c1 census168: (3,7) graphs on 168 vertices with a G-invariant G-set, G containing an element of order 7

Status: PARTIAL. Two isomorphism classes found, both already known. No new graph. The census is not exhaustive for the
groups in scope (see "Not covered"). Run time 23:41 to 00:35 UTC, one orbdfs process at a time.

## Isomorphism classes (src/iso.py; all 195 solution files passed bin/apsp 3 7)

| class | files | |Aut| | girth | groups that found it | example file |
|---|---|---|---|---|---|
| 1 | 147 | 168 | 8 | SmallGroup(21,1) = C7:C3 (144 files); SmallGroup(168,43) = AGammaL(1,8), targeted G-set (3 files) | squad/r1/c1/sol/n168_g21_1_g_k1_20_1.edges |
| 2 | 48 | 504 | 12 | SmallGroup(21,1) = C7:C3 (48 files) | squad/r1/c1/sol/n168_g21_1_g_k1_20_12.edges |

Class 1 is isomorphic to records/n168_new_girth8_aut168.edges (iso.py certificate 6077b69d4f). Class 2 is isomorphic to
inputs/c1_base168.edges = C168.1 (certificate 04ff72ecb6). Both are valid (3,7) graphs on 168 vertices. Aut orders from
dreadnaut (src/gutil.py aut_gens). The girth-8 class has vertex orbits 56/28/84 for AGammaL(1,8), as recorded.

Files that found the classes are listed in squad/r1/c1/classes.tsv. The run table is squad/r1/c1/runs.tsv.

## Per-group summary (squad/r1/c1/group_summary.md, from squad/r1/c1/report.py)

"complete" = the G-set ran to DONE, or all 16 shards ran to DONE (after the SHARD fix; see below). "est >= 3e7" = skipped
by the rule in the brief (Knuth estimate from PROBE=300; the estimate is unreliable, see the 14_1 and 21_2 runs).

| group | G-sets listed | est >= 3e7 (not run) | complete | incomplete | solution hits (sum of runs) |
|---|---|---|---|---|---|
| SmallGroup(14,1) = C14 | 50 | 17 | 14 | 2 (one TIMEOUT, one partial shard run) | 0 |
| SmallGroup(21,1) = C7:C3 | 25 | 1 | 24 | 0 | 192 (2 classes) |
| SmallGroup(21,2) = C21 | 25 | 3 | 17 | 0 | 0 |
| SmallGroup(42,1) = C7:C6 | 300 (cap) | 0 | 300 | 0 | 0 |
| SmallGroup(42,2) | 300 (cap) | 100 | 200 | 0 | 0 |
| SmallGroup(42,3) | 300 (cap) | 222 | 63 | 3 (1 UNRESOLVED, 1 TIMEOUT, 1 partial shard run) | 0 |
| SmallGroup(168,42) = PSL(2,7) | 145 (all G-sets listed) | 0 | 145 | 0 | 0 |
| SmallGroup(168,43) = AGammaL(1,8) | 295 (cap 300 hit) | 75 | 220 | 0 | 0 |
| TOTAL | 1440 | 418 | 983 | 5 | 192 |

Targeted G-set for SmallGroup(168,43) with the vertex-orbit types of the girth-8 graph (stabilisers C3, C6 on side A; C2 on
side B; squad/r1/c1/gs/special168_43/sp_1.txt): 6 nodes, 3 solutions, all class 1. This G-set was NOT among the 295
capped G-sets, so the SmallGroup(168,43) line above is not a census of that group.

## Not covered (honest list)

- Order 7 (G = C7 alone) was not run. It is out of reach: 24 orbits of size 7, far beyond the orbdfs budget. The census
  therefore covers only graphs with a subgroup of order 14, 21, 28, 42, 56, 84 or 168 that contains an element of order 7.
- SmallGroup(14,2) = D14, SmallGroup(28,*), SmallGroup(42,4..6), SmallGroup(56,*), SmallGroup(84,*) and the other
  SmallGroup(168,*) were not run (time). Only the groups listed in the table were run.
- The G-set enumeration (src/gsets.g via gen37.sh) was capped at 300 G-sets per group in enumeration order (A-side outer
  loop), so for 42_1..3 and 168_43 the listed sets are a prefix of the full enumeration, not all of it.
- 418 G-sets with Knuth estimate >= 3e7 were not run (the brief's threshold). The estimate is noisy: g14_1 G-set 29
  (est 1.6e5) took several sharded runs, and g21_2 G-set 13 (est 7.9e4) timed out unsharded.
- Incomplete: squad/r1/c1/gs/n168/g42_3/g_k1_224.txt (UNRESOLVED after the 300 s shard budget), g42_3/g_k1_198.txt
  (TIMEOUT, no shards run), one more SmallGroup(42,3) G-set with a partial shard run (see runs.tsv), squad/r1/c1/gs/n168/g14_1/g_k1_30.txt
  (TIMEOUT, no shards run), and g14_1/g_k1_29.txt (sharded, pieces 0..12 logged before stop). g42_3/g_k1_199 has 16
  shard rows, all DONE, but some of them may be pre-fix (see below).

## Tool issues found during the run (for Opus)

- bin/orbdfs was rebuilt during the run. Its header then had an EXCLUDED_TWIN rule (src/orbdfs.c, twin lemma, bound
  < n/2 then prints DONE nodes=0). I did not verify that rule. 21_2 g_k1_3 (est 5.5e4) returns EXCLUDED_TWIN; the result
  is logged as EXCL_TWIN and was not checked with NOTWIN=1.
- SHARD=i/m bug, reported by Opus at about 00:17: every shard run before the fix was superseded. I moved the affected G-sets'
  rows out of runs.tsv (old rows kept in squad/r1/c1/runs_before_shardfix.tsv), and reran g21_2/g_k1_3, g21_2/g_k1_13,
  g14_1/g_k1_29, g14_1/g_k1_30 and g42_3/g_k1_251 with the fixed binary (est_rerun_shardfix.txt). Reruns for g14_1/g_k1_29 and
  g14_1/g_k1_30 were stopped at the time limit (see Not covered). The SmallGroup(42,3) G-sets 199 and 251 were run by the chain
  driver from 00:12; runs.tsv has no timestamps, so I cannot say which of their shard rows predate the fix at 00:16:55.
  Every shard row so far reports 0 solutions, and all 192 solution hits come from unsharded runs of SmallGroup(21,1), so the
  bug changes only the "complete" claims for sharded G-sets, not the classes found.
- A mid-run GAP stop lost the Print output of the 168_43 generation (the file list), so that list was rebuilt from the
  directory listing (descriptions lost; orbit types checked from the files instead).
