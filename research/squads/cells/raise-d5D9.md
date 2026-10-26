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

Next bar: |G| ≥ 14,741 (graph ≥ 29,482). Session stopped at that bar (see the log: no further solve).

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
- Phase 7 (12 screened groups above 14,740, seeds 21–25, 150 s each): no solve. Best cost 2 at 14,770 (Z_1055⋊Z_14 and Z_422⋊Z_35 at 14,770 in the phase-7 run, not 14,740 ones).
- Phase 8 (Z_1055⋊Z_14, Z_422⋊Z_35, Z_422⋊Z_11, Z_1055⋊Z_14 second r; seeds 26–37, 150 s each): no solve; best cost 2 (5 runs), then 4, 6, 8.
- Phase 9 (16 untried screened groups above 14,740, seeds 40–41, 150 s each): no solve; costs 4–16, mostly 10–16.

## Where this stands

- **Record: 29,480 vertices** (Haar graph of Z_335 ⋊ Z_44, S listed above), up from 28,560. Verified by two independent
  checkers (build_haar2.py, apsp.c). Files: research/frontier/sols/d5D9_*_s*_n*.txt (five solutions this session;
  the 29,480 one is the latest). Coordinator re-check still needed.
- **What worked:** screening random-generator cost statistics over all candidate metacyclic and SL/PSL groups of
  order (14,280, 15,186]; annealing with haar_gen3 at 150–480 s runs and many seeds, since solve times are heavy-tailed
  (0.5 s to 315 s on the same group).
- **Where it stopped:** above |G| ≈ 14,740 the best groups stay at cost 2 after many seeds. The tooling does not reach
  the next group order. The size law predicted 27,460 for this cell; our solves sit well above that, so the law's
  band is not a reliable wall for this cell.
- **Not tried:** voltage lifts over larger base graphs and symmetric (orbit) S for these orders (the orbit search is the
  brief's main method for D = 7–10; it was not run here), longer per-seed runs on the cost-2 groups at 14,770, and a
  second annealing variant. These are the next steps if the coordinator wants more.

## Round 2 (job raise2-5-9, branch claude/raise2-5-9-record-lt2t4o)

Starting record: **29,480** (N = 14,740, Z_335 ⋊_8 Z_44, round 1). Round-1 notes above are kept unchanged.

### Orbit (symmetric S) routes for Δ = 5: closed

Δ = 5 has only three orbit shapes, S = {e} + (f−1) α-fixed generators + m α-orbits of size k, with f + k m = 5:
(k, m, f) = (2, 2, 1), (2, 1, 3), (3, 1, 2), (5, 1, 0).

- **k = 2, (2, 2, 1)**: α = (a, j) ↦ (−a, j) on Z_335 ⋊ Z_44 (the automatic choice, 43 fixed elements), 4 seeds × 120 s,
  K = 8: best uncovered **1,108–1,216** after 7.4·10⁶ evaluations; random S on the same group reaches cost 2 in the same
  time. The lab rule (STRUCTURE.md §1, §5: involutions do not work at odd D) holds here.
- **k = 3, (3, 1, 2)**: added an `EXHAUST=1` mode to `research/structured/haar_sym.c` (`exhaust_main`). It enumerates
  every S of the shape: all fixed t ∈ Fix(α) times one representative per α-orbit (≈ |Fix|·N/3 shapes), each costed
  exactly. D = 9 results: PSL(2,31) (N = 14,880, 14 fixed elements) best cost **42** over 69,370 shapes; SL(2,13) × Z_7
  (N = 15,288) best cost **24** over 56,012 shapes. Random S gets cost 2 on groups of this order. A single orbit has too
  few degrees of freedom to reach 0 at μ ≈ 39–45, so this shape is ruled out.
- **k = 5, (5, 1, 0)**: one orbit, N/5 shapes; same argument, not run.

Conclusion: symmetric S cannot beat random S for Δ = 5 at D = 9. The only route left for this cell is random S
annealing on untried groups, or voltage lifts.

### Correction to round 1's candidate list

`research/frontier/raise_d5D9/gen.py` `prime_power(q)` tests p = 2 first and returns None for every odd q. So every
SL(2,q), PSL(2,q), PGL(2,q) with q odd was silently dropped from the 2,398-candidate list. Only even-q SL groups and the
metacyclic groups were ever screened. Corrected list: 43 SL/PSL/PGL × Z_n groups in (14,740, 15,700] with n ≤ 130
(`screen_sl.txt`, recorded in the LOG). Random-S screen (RANDSAMPLE=2000), best p1: SL(2,25) (15,600) p1 58 min 26;
SL(2,13) × Z_7 (15,288) p1 62 min 30; PSL(2,11) × Z_23 (15,180) p1 66 min 45; PSL(2,9) × Z_41 (14,760) p1 77 min 37;
PSL(2,31) (14,880) p1 103. The untried metacyclic groups start at p1 ≈ 53 (round 1's best tried were p1 20–30).

### Metacyclic and SL candidates tried in round 2 (short runs, haar_sym FAST=2, K = 8)

The round-1 generator bug above means the untried SL/PSL candidates were tested first. Results at 120–300 s:
SL(2,25) (15,600) best cost 16, SL(2,13) × Z_7 (15,288) 10, PSL(2,11) × Z_23 (15,180) 18, PSL(2,9) × Z_41 (14,760) 14.
SL and PSL candidates here sit at cost 10–18; the record-tier groups sit at 2. Not pursued further.

Untried metacyclic groups from round 1's screen (`queue_meta_untried.txt`, p1 ≥ 53): the first four finished at 150 s
with best cost 16 (Z_738⋊20·125, N = 14,760), 6 (Z_345⋊44·7, N = 15,180), 12 (Z_2129⋊7·634, N = 14,903), 10
(Z_2143⋊7·143, N = 15,001). A further 36 were queued and then stopped in favour of the longer runs below.
(The first queue launch used a bad job-line format and was discarded; no results from it.)

### Long runs on round 1's cost-2 groups at 14,770 (1,200 s each, seeds 201–204)

Round 1 reached cost 2 at N = 14,770 on Z_422⋊35 (r = 5: 4 runs; r = 11: 2 runs) and Z_1055⋊14 (r = 199: 1 run), each
at 150 s. Those were the only near-misses above 14,740. Four 1,200-s runs with fresh seeds were started (see the LOG
entry for the outcome).

### New record: 29,540 vertices (round 2)

Haar graph of G = Z_422 ⋊_5 Z_35 (order 14,770; r = 5 is a unit mod 422 with order exactly 35), 5-regular,
diameter 9, bipartite. S as (a, j), a ∈ Z_422, j ∈ Z_35: (0,0), (318,34), (101,22), (327,1), (290,8).
Found by haar_sym (FAST=2, K = 8, THREADS=1) at seed 204 after 220 s and 2.3·10⁷ evaluations, a long run (1,200 s
budget) on a group that had reached cost 2 in round 1 at 150 s.
File: research/frontier/sols/d5D9_meta_422_35_5_s204_n29540.txt (sha256 of the edge list
f3004a3b3dec30384cc7747e9d863c593d6c4a521b701c61c4dbf5ee80d73e87).
Checks: research/frontier/build_haar2.py VALID (ecc 9 from both sides, n = 29,540, max = min degree 5, no repeats);
research/lifts/coordinator_check/apsp.c (all-pairs BFS) VALID, bipartite, diameter 9.
Coordinator re-check still needed. The next bar is |G| ≥ 14,771 (graph ≥ 29,542).

### Untried groups just above the new order (600 s each, seed 301)

Groups above N = 14,770 that round 1 never ran, taken from its screen (p1 ≤ 60): Z_346⋊43 r=29 (14,878) best cost **2**
(r=23: 4); Z_1651⋊9 r=68, r=22 (14,859): 6; Z_1235⋊12 r=7 (14,820): 7; Z_496⋊30 r=7 (14,880): 6; Z_1241⋊12 r=81 and
r=64 (14,892): 6 and 8. Z_346⋊43 r=29 is the lead for the next bar.

Next: 1,200-s runs on Z_346⋊43 r=29 (seeds 401–403) and Z_991⋊15 r=71 (seed 401).

### New record: 29,756 vertices (round 2, second record)

Haar graph of G = Z_346 ⋊_29 Z_43 (order 14,878; r = 29 is a unit mod 346 with order exactly 43), 5-regular, diameter 9,
bipartite. S as (a, j), a ∈ Z_346, j ∈ Z_43: (0,0), (249,8), (58,9), (284,41), (265,16).
Found by haar_sym (FAST=2, K = 8, THREADS=1) at seed 613 after 7.8 s (7.1·10⁵ evaluations), in a short-restart batch of
eight seeds × 300 s on this group. Earlier seeds on the same group: 10 runs, best cost 2 (none solved), so the solve was
a heavy-tail event, as in round 1.
File: research/frontier/sols/d5D9_meta_346_43_29_s613_n29756.txt (sha256 of the edge list
1f1d8ef6d96780894804f60e7220be34bfe0c7aa6d5d44dcd11f86e5036e1e4a).
Checks: build_haar2.py VALID (ecc 9 from both sides, n = 29,756, max = min degree 5, no repeats); apsp.c VALID
(bipartite, diameter 9). Coordinator re-check still needed. The next bar is |G| ≥ 14,879 (graph ≥ 29,758).

### Status at the end of round 2 (2026-10-25, about 2.5 h of the 6 h budget)

- **Record: 29,756 vertices** (Z_346 ⋊_29 Z_43, seed 613), up from 29,480 at the start of round 2 and 28,560 before round 1.
  Solutions in research/frontier/sols/: d5D9_meta_422_35_5_s204_n29540.txt and d5D9_meta_346_43_29_s613_n29756.txt.
  Both checked by build_haar2.py and apsp.c. The coordinator's re-check is still needed.
- **Closed:** orbit-symmetric S for Δ = 5 at D = 9 (see the first round-2 section). Odd-q SL/PSL/PGL screen: no lead.
- **Next bar:** |G| ≥ 14,879 (graph ≥ 29,758). Restarts since 14,878 was solved: 12 runs at 300 s on Z_1241⋊81 (14,892,
  best 4), Z_496⋊7 (14,880, best 4), Z_1491⋊76 (14,910, best 8); 10 more at 300–600 s on Z_346⋊29 (14,878, the solved group,
  an equal-order neighbour does not help). Lowest costs for untried groups above 14,878: 4–6.
- **Where it stands:** the search is heavy-tailed. The two round-2 records came from short restarts on groups that had
  shown cost 2–4 earlier, and nothing above 14,878 has reached cost 2 in ~40 runs. This is not "truly stuck" yet, but
  the yield per 300-s run is now low. Options if the coordinator wants more: many more 300-s seeds on the cost-2 groups
  (the Z_346⋊43 r=29 result came from seed 613 after 3 of 10 runs stayed at cost 2), and the metacyclic groups in the
  remaining screen tail (about 1,100 untried, p1 ≥ 53).

## Round 3 (job raise3-5-9, branch claude/raise3-5-9-vcnwf7)

Starting record: **29,756** (N = 14,878, Z_346 ⋊_29 Z_43, round 2). Next bar: |G| ≥ 14,879 (graph ≥ 29,758).
Tooling: research/structured/haar_sym.c (FAST=2 default, same CLI as haar_gen3); binary built outside the repo.
Working dir: research/frontier/raise3_d5D9/ (run_sym.sh, stage1_jobs.txt, untried_window.txt, logs in runs/).

Plan (4 cores, 100–150 s per run, seeds distinct per group):
- Stage 1: the top 120 untried metacyclic groups in (14,878, 15,186] by screen p1 (queue from round 2, none run before).
- Stage 2: cost-2 groups get 4–6 more seeds at 150–300 s.
- Also noted, not yet run: non-prime-power-field AGL(1,q) with q = 4, 8, 9, 16, 25, 32 (non-metacyclic). Their
  cyclic factors are large (n ≥ 62 except q = 25, 32 with n = 25, 15), so they look more like the SL/PSL
  cells than the record groups; low priority.

### Round 3 log (2026-10-26, haar_sym FAST=2, THREADS=1, 4 workers)

- **Stage 1** (`stage1_jobs.txt`, 120 untried metacyclic groups in (14,878, 15,186] with the best screen p1, 100 s each,
  seed 1001): no solve. Best cost 8 at Z_1491⋊76 (N = 14,910), Z_2129⋊7·933 (14,903), Z_1658⋊9·5 (14,922); the rest
  mostly 10–20. These untried groups look weaker than the round-2 leads.
- **Stage 2** (`stage2_jobs.txt`, 8 groups × 6 seeds × 200 s, plus 6 non-metacyclic AGL(1,q) runs): no solve.
  Best cost 6 at Z_1491⋊76 (N = 14,910), Z_1658⋊9·5 (14,922), Z_496⋊30·7 (14,880). Non-prime-field AGL(1,q) × Z_n
  (q = 4, 8, 9, 16, 25, 32) is far off: best costs 148 to 20,216 (q = 32 at 148 and q = 25 at 425 are the closest).
  Closed: this family is not competitive.
- **Calibration** on the known-solvable Z_346⋊43 (N = 14,878), 120 s runs, 8 seeds per setting: K = 4 best costs
  4–6 (no solve); K = 8 one cost 2, rest 4–6 (no solve); K = 16 one cost 2, rest 4–8 (no solve). K = 8 is kept.
  Round 2's solve on this group took 7.8 s at seed 613 out of about 10 runs of 300 s, so the per-run chance at 120 s
  is far below 1 in 24.
- **Stage 3** (4 leads × 4 seeds × 300 s): Z_1658⋊9·5 (N = 14,922) reached **cost 2** once (seed of 4 runs), the first
  cost-2 result above 14,878 in this round. Z_1241⋊12·81 and Z_496⋊30·7 at cost 4; Z_1491⋊76 at 8.
- **Stage 4** (Z_1658⋊9·5, 12 seeds × 300 s): best 6. The cost-2 result did not repeat: 0 solves in 12 runs.
- **Stage 5** (next 120 untried groups by p1, 100 s each): stopped after 20 runs. Costs 48–62 in the first 20, so
  the rest of this block could not reach cost 2 and was killed.

## Where this stands (round 3, end)

- **Record: unchanged at 29,756** (N = 14,878). No new solution file this round. Next bar: |G| ≥ 14,879.
- **Stopped at about 3 h of the 6 h budget.** Reason: the untried metacyclic pool is exhausted at useful quality. The top
  120 by screen p1 reach cost 8 at best (100 s runs); the next 20 are at cost 48+; the leads with cost 2–4 history
  (Z_496⋊30·7, Z_1241⋊12·81, Z_1658⋊9·5) gave 0 solves over about 30 runs of 200–300 s since round 2's 12 runs. The
  calibration group (N = 14,878) gives one cost-2 hit in 24 runs at 120 s for K = 4, 8, 16.
- **Closed this round:** non-prime-field AGL(1,q) × Z_n (q = 4, 8, 9, 16, 25, 32), a non-metacyclic family with an
  elementary-abelian normal subgroup: costs 148 to 20,216. K = 4 is worse than K = 8; K = 16 is no better than K = 8.
- **Not tried (for the coordinator):** (1) voltage lifts of small base graphs with more than two vertices (the
  metacyclic lifts route is in research/lifts/); (2) a new group family in haar_gen3 for Z_m ⋊ (non-cyclic abelian H),
  e.g. Z_m ⋊ (Z_a × Z_b), which is outside metacyclic; (3) groups of order Z_p² ⋊ Z_k (p² k in the window, e.g.
  Z_11² ⋊ Z_124, Z_17² ⋊ Z_52), which need a new multiplication table; (4) long single runs (1,200 s+) on the cost-2
  leads, which round 2 found to be the path to a record.
- Files: research/frontier/raise3_d5D9/ (run_sym.sh, stage1–5 jobs and logs, runs/, untried_window.txt, tried_meta.txt,
  calib_K*.log). Solver binary built from research/structured/haar_sym.c (gcc -O3 -march=native -fopenmp, FAST=2 default).
