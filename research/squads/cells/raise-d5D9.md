# Cell (Δ, D) = (5, 9): raise the record (job raise-5-9)

Branch `claude/raise-d5d9-record-jhegor`. Table value 27,936 (DS14v2). Bipartite Moore bound 174,762.
Record held at the start: **28,560** vertices, Haar graph H(G,S) of G = Z_595 ⋊_53 Z_24 (order 14,280), S = {(0,0),
(556,1), (172,11), (75,23), (170,5)}. Solution file research/lifts/sols/haar/hc_d5D9_meta_595_24_53_1_s1.txt; rebuilt
with research/frontier/build_haar2.py this session: VALID (ecc 9 from both sides, 5-regular, 28,560 vertices).

## Status

**New record: 29,480 vertices** (5-regular, diameter 9, bipartite), Haar graph of G = Z_335 ⋊_8 Z_44 (order 14,740),
seed 17 of phase 6, found in 68 s. S as (a, j), a ∈ Z_335, j ∈ Z_44: (0,0), (267,25), (204,41), (57,24), (68,17).
Checked by build_haar2.py (VALID, ecc 9 from both sides, edge-list sha256
079dad1f55bc9426caa314b74c21f3367d47e677df833e069ec5f6f49113d996) and by research/lifts/coordinator_check/apsp.c
(all-pairs BFS, VALID, n = 29,480). Saved as research/frontier/sols/d5D9_meta_335_44_8_s17_n29480.txt.
Also valid, below the record: Z_421 ⋊_48 Z_35 at 14,735 (graph 29,470; seed 16, 0.8 s; build_haar2 and apsp VALID,
not saved as a file).
Earlier records in this session: 29,214 (Z_541 ⋊ Z_27), 28,938, 28,920, 28,918. Not yet re-checked by the coordinator.

The bar for the next step is |G| ≥ 14,741 (graph ≥ 29,482).

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
- Phase 2 (8 cost-2 groups at N = 14,421–14,634, seeds 2–5, 480 s each; `phase2_groups.txt`): stopped after 14,459 was
  solved, since those runs could no longer raise the record. Partial results: `phase2.log`.
- Phase 3 (groups with |G| > 14,459, seeds 2–5, 480 s each; `phase3_groups.txt`, `phase3.log`): Z_964⋊Z_15 solved
  at 14,460 (seed 2, 166 s) → record 28,920 (see above). Its other seeds, and the other groups, continue.
- Phase 3 (groups with |G| > 14,459, seeds 2–5, 480 s each; `phase3_groups.txt`, `phase3.log`): Z_964⋊Z_15 solved at 14,460
  (seeds 2 and 4, 161–166 s); Z_371⋊Z_39 solved at 14,469 (seed 5, 0.5 s) → record 28,938. The other 14,460+ groups
  ended at cost 2–4 after 480 s.
- Phase 4 (40 more screened groups above 14,459, one seed, 300 s each; `phase4_groups.txt`, `phase4.log`): no
  solution; costs 2–14, mostly 6–10. The second screen tier is much worse than the first, so screen rank is only a
  weak guide beyond the top ~40. (A first launch failed because the group lines lacked the cyclic factor "1"; fixed
  and re-run.)
- Phase 5 (6 cost-2 groups above 14,469 — 1322⋊11·81, 541⋊27·28, 542⋊27·25, 1321⋊11·205, 1322⋊11·9, 1324⋊11·293 —
  seeds 6–13, 150 s each; `phase5_jobs.txt`, `phase5.log`): running. Heavy-tailed: short restarts are the cheapest
  way to see a solve (the 14,469 record came in 0.5 s on seed 5, while seeds 2–4 stayed at cost 2 for 480 s).
- Phase 5 result: Z_541⋊Z_27 solved at 14,607 (seed 13, 43 s) → record 29,214. Other seeds of that group and the other
  five groups: see `phase5.log`.
- Phase 6 (8 groups with |G| ≥ 14,607, seeds 14–19, 150 s each; `phase6_groups.txt`, `phase6.log`): two solves so far,
  Z_421⋊Z_35 at 14,735 (seed 16, 0.8 s) and Z_335⋊Z_44 at 14,740 (seed 17, 68 s) → record 29,480.
