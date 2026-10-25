# Cell (Δ, D) = (5, 9): raise the record (job raise-5-9)

Branch `claude/raise-d5d9-record-jhegor`. Table value 27,936 (DS14v2). Bipartite Moore bound 174,762.
Record held at the start: **28,560** vertices, Haar graph H(G,S) of G = Z_595 ⋊_53 Z_24 (order 14,280), S = {(0,0),
(556,1), (172,11), (75,23), (170,5)}. Solution file research/lifts/sols/haar/hc_d5D9_meta_595_24_53_1_s1.txt; rebuilt
with research/frontier/build_haar2.py this session: VALID (ecc 9 from both sides, 5-regular, 28,560 vertices).

## Status

**New record: 28,918 vertices** (5-regular, diameter 9, bipartite), Haar graph of G = Z_761 ⋊_25 Z_19 (order 14,459),
seed 2 of the phase-2 runs, found in 10 s. S (as the solution file lists the index and the element (a, j) with
a = the Z_761 part, j = the Z_19 part): (0,0), (457,18), (647,8), (151,5), (97,5). Checked by build_haar2.py (VALID,
ecc 9 from both sides, edge-list sha256 2aa4940eb41213417c30b78c905efb899ad945c2b4066925ddbba67360feda7a) and by
research/lifts/coordinator_check/apsp.c (all-pairs BFS, VALID, n = 28,918, degree 5, diameter 9). Saved as
research/frontier/sols/d5D9_meta_761_19_25_s2_n28918.txt. Not yet re-checked by the coordinator.

The bar for the next step is |G| ≥ 14,460 (graph ≥ 28,920).

## Method

- Tool: research/frontier/haar_gen3.c (annealing over S for a fixed group G; N = |G|, graph order 2N). Built here with
  `gcc -O3 -march=native -fopenmp`; the binary copy used is research/frontier/raise_d5D9/haar_gen3_bin.
- Target: |G| ≥ 14,281 (graph order ≥ 28,562). Size-law ceiling (SIZE_LAW.md, first moment) N_h = 15,186, so the
  realistic window is 14,281 … ~15,000.
- Candidates: every group in (14,280, 15,186] that haar_gen3 builds with a non-abelian base of order ≥ 60 and a
  cyclic factor ≤ 60, or a metacyclic Z_m ⋊_r Z_k (two r per (m,k), r of exact order k). 2,398 candidates, almost all
  metacyclic (`research/frontier/raise_d5D9/`: phase1_jobs.txt, screen tables in the session scratch).
- Screen: `RANDSAMPLE=5000 haar_gen3 5 9 …` cost statistics of random generator sets (no search); ranked by p1
  (1 % quantile; lower is better). Top group: Z_761 ⋊ Z_19 (14,459), a Frobenius group with no involutions.
- Calibration (4 threads, 90 s, K = 8): the record's own group Z_595 ⋊ Z_24 solves at 14,280 in 20 s (762 k evaluations),
  so the search reproduces the record. At 14,459 the best top candidates end at cost 2 after 90 s.

## Log

- 2026-10-25, session start: record verified (build_haar2 VALID). Screen of 2,398 candidates done.
  Calibration as above.
- Phase 1 (40 top-screened groups, 120 s each, seed 1, K = 8; `raise_d5D9/phase1.log`, `runs/`): no solution above
  14,280. Best cost 2 at N = 14,421 (Z_437⋊Z_33), 14,459 (Z_761⋊Z_19, two r), 14,460 (Z_964⋊Z_15, two r),
  14,469 (Z_371⋊Z_39), 14,542 (Z_1322⋊Z_11), 14,607 (Z_541⋊Z_27), 14,634 (Z_542⋊Z_27). Cost 4–8 elsewhere; the
  larger orders (14,735 and up) reached cost 2 at best.
- Phase 2 (the 8 cost-2 groups at N = 14,421–14,634 with the cost-2 mark above, seeds 2–5, 480 s each; the group list
  is `raise_d5D9/phase2_groups.txt`): running.
