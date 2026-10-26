# raise-d15D8: beat 18,128,880 at the bipartite (Δ, D) = (15, 8) cell

Job "raise-15-8" (Haiku worker, cloud session, 2026-10-25). Branch `claude/raise-d15d8-haar-fhvmnv`.

## Standing record

- **18,128,880** = 2·|SL(2,109) × Z_7|, S = orbits of an order-3 automorphism, k = 3, m = 5, f = 0, μ = 33.0.
  File: `research/frontier/sols/d15D8_sl_109_7_orb3f0_s1.txt`. Table value 14,172,480.
- Other solved (15,8) graphs in sols/ (smaller): psl 137×Z7 (17,998,512), psl 61×Z79 (17,926,680),
  psl 83×Z31 (17,722,824), sl 41×Z127 (17,495,520), psl 47×Z163 (16,915,488).

## Why the target is narrow

Haar graph on G with |S| = 15 and D = 8 has 2N vertices, so beating the record needs N > 9,064,440.
With W = 113,522,235 binding words, μ = N·exp(−W/N) and d ln μ / d ln N ≈ 1 + W/N ≈ 13.5. So N moves only a
few percent while μ climbs from 33 toward the orbit method's wall (μ ≈ 45–50). Candidate orders above the record
(orb_screen.py `--list`, μ at each order, prime-field groups with every prime of n ≡ 1 mod 3):

| group | N | 2N | μ |
|---|---|---|---|
| sl 53 × Z61 | 9,078,264 | 18,156,528 | 33.7 |
| sl 29 × Z373 | 9,086,280 | 18,172,560 | 34.1 |
| psl 263 | 9,095,592 | 18,191,184 | 34.5 |
| psl 43 × Z229 | 9,098,628 | 18,197,256 | 34.7 |
| psl 79 × Z37 | 9,119,760 | 18,239,520 | 35.8 |
| sl 31 × Z307 | 9,136,320 | 18,272,640 | 36.7 |

## Tools

- `research/structured/haar_sym.c` (built as `research/structured/haar_sym`, `gcc -O3 -march=native -fopenmp`),
  orbit search with `ORBIT="3 5 0"`, single thread. About 30–100 evaluations/s at N ≈ 9M.
- `research/structured/tools/raise_run.sh SECS SEED TAG GROUP...` runs one job into `runs/raise_d15D8/`.
- Verification: haar_sym's own full diameter check (prints VALID line), then build_haar2.py and
  `research/frontier/haarcheck_sl.c` / `haarcheck2.c` (`hcsl`, `hc2`) for SL, `haarcheck_psl.c` for PSL,
  because all candidates are above the 20M-vertex rule-of-thumb only for N ≥ 10M; here 2N ≈ 18M.

## Log

(see the bottom; newest last)

### Tier 1 (ORBIT 3 5 0, seed 1, 4000 s each, 4 in parallel): no solve

| group | N | μ | Fix | best cost | evals |
|---|---|---|---|---|---|
| sl 29 × Z373 | 9,086,280 | 34.1 | 29 | 3 | 197k |
| sl 53 × Z61 | 9,078,264 | 33.7 | 53 | 3 | 223k |
| psl 263 | 9,095,592 | 34.5 | 131 | 4 | 108k |
| psl 43 × Z229 | 9,098,628 | 34.7 | 20 | 6 | 209k |

Cost 3 with one or two fixed-point misses is the same stall the orbit notes describe (§3, §7). Four 4000 s runs
(about 7·10⁵ evaluations in total) did not reach cost 0 at these orders.

### Tier 2 (ORBW=3, 4000 s each, 4 in parallel), started

`runs/raise_d15D8/tier2.sh`: sl 29×Z373 (seed 2), sl 53×Z61 (seed 2), sl 29×Z373 with RESTART=1 (seed 3),
psl 263 (seed 2). ORBW=3 weights an uncovered α-fixed element as much as a free orbit; the (11,8) cell was
solved with it.

### Tier 2 (ORBW=3 for three runs, 4000 s each): no solve

| run | group | best cost | evals |
|---|---|---|---|
| sl29_373_orbw3_s2 | sl 29 × Z373 | 3 | 190k |
| sl53_61_orbw3_s2 | sl 53 × Z61 | 3 | 214k |
| sl29_373_orbw3_restart_s3 (RESTART=1) | sl 29 × Z373 | 6 | 189k |
| psl263_orbw3_s2 | psl 263 | 6 | 103k |

### Tier 3 (μ ≈ 33.2, the two orders closest to the record's μ), started

`runs/raise_d15D8/tier3.sh`: prod psl 5 × psl 11 × Z229 (N = 9,068,400; seeds 1, 2 and an ORBW=3 seed 3) and
sl 32 × Z277 (N = 9,067,872; GF(32) as `poly x^5+x^2+1`, no wide rows, so slower per evaluation).

### Tier 3 results so far (about 1840 s)

- prod psl 5 × psl 11 × Z229 (three runs, seeds 1, 2 and ORBW=3 seed 3): costs in the thousands (2214–3474)
  after 6.5·10⁴ evaluations. PSL(2,5) = A5 as a factor makes the orbit energy far too high. Stopped.
- sl 32 × Z277 (GF(32), seed 1): cost 4 at 5·10⁴ evaluations, the best of tier 3. Still running.

### Tier 4 (started, 3600 s): sl 32 × Z277 seed 2 and sl 53 × Z61 ORBW=3 seed 4.

### Tier 4 results

- **sl 53 × Z61, ORBW=3, seed 4: cost 0 after 2.07·10⁵ evaluations** (μ = 33.7, Fix = 53).
  haar_sym's own full diameter check: OK (both the direct and s₀ = e normalised forms).
  Candidate: 2N = **18,156,528** vertices, i.e. above the record 18,128,880 by +0.15 %.
  Solution file: `runs/raise_d15D8/sl53_61_orbw3_s4.sol`. Independent verification in progress
  (build_haar2.py, haarcheck_sl.c, haarcheck2.c); this entry is updated when they finish.
- sl 32 × Z277 (GF(32)), seeds 1 and 2: best cost 4 and 6 after 1·10⁵ and 0.99·10⁵ evaluations. Not solved.
- sl 32 × Z277 and sl 53 × Z61 (seed 2 / seed 3) earlier: see above tiers.

### RECORD: 18,156,528 vertices at (15,8) (sl 53 × Z61, ORBW=3, seed 4)

Beats the standing record 18,128,880 by +27,648 vertices (+0.15 %).

- Graph: Haar graph of G = SL(2,53) × Z61, |G| = N = 9,078,264, |S| = 15 = 3·5 (5 free orbits of an order-3 automorphism, f = 0),
  2N = 18,156,528 vertices, 15-regular, 136,173,960 edges, no duplicate edges.
- Verification (all pass, all report d = 15, D = 8):
  - haar_sym's own full diameter check (direct and s₀ = e normalised): OK.
  - build_haar2.py (edge-list sha256 `5cd1a1ad900db9fd82d6155d4e342339157bf2078a142affa83298d6ce25e8d7`): VALID.
  - `research/frontier/haarcheck_sl.c` (hcsl): VALID, reached 9,078,264 / 9,078,264 from each side, ecc 8.
  - `research/frontier/haarcheck2.c` (hc2): VALID, reached 18,156,528 / 18,156,528, ecc 8 both sides.
- Saved as `research/frontier/sols/d15D8_sl_53_61_orbw3f0_s4.txt`. Logs and checker outputs are in
  `research/structured/runs/raise_d15D8/sl53_61_orbw3_s4.*`.
- Search: μ = 33.7, Fix = 53, ORBW=3 (uncovered fixed element weighs 3), seed 4, solved after 2.07·10⁵ evaluations in 3565 s.
  The other runs of the same group ended at best cost 3 (seed 1, no ORBW) and 3 (ORBW=3, seed 2), with no solve.
  The solve is one seed, not a measured advantage for ORBW=3.

---

## Round 2 (job "raise2-15-8", Haiku worker, 2026-10-25)

Branch: `claude/raise-d15d8-resume-kwwllj` (the session's designated branch; round 1 is `claude/raise-d15d8-haar-fhvmnv`).

**Bar to beat: 18,156,528** (sl 53 × Z61, round 1, self-verified: haar_sym, build_haar2.py, hcsl, hc2). The brief's
18,128,880 is still what master's README table shows, so round 1's record is above the recorded number. Pending coordinator check.

**Not repeated from round 1:** sl 29 × Z373 (seeds 1, 2, 3), sl 53 × Z61 (seed 4 solved), psl 263, psl 43 × Z229,
sl 32 × Z277, prod psl 5 × psl 11 × Z229. Those are not re-run here unless a new seed is needed for an
untested setting.

**Plan:**
1. Random-sample screen (300 RANDORB samples, k = 3, f = 0, μ ≈ 34–37) over all non-product groups with
   2N in [18,156,528, 18,500,000]. Files: `research/structured/runs/raise_d15D8_r2/screen/summary.txt`.
2. Long annealing runs (4000 s, single thread, 4 in parallel) on the best screened groups, several seeds,
   ORBW = 3 and plain, via `tools/orbq.sh`. Any solve is checked with hcsl/hc2 (SL) or haarcheck_psl (PSL)
   and build_haar2.py if N ≤ 10M.


### Screen result (300 RANDORB samples per group, k = 3, f = 0; `runs/raise_d15D8_r2/screen/summary.txt`)

Random-S lower tail, μ ≤ 36 and the groups with the best tail at μ ≈ 36–38.5 (2N = Haar order):

| group | N | 2N | μ | fix | min | p1 | p10 | median |
|---|---|---|---|---|---|---|---|---|
| sl 53 × Z61 (solved, round 1) | 9,078,264 | 18,156,528 | 33.7 | 53 | 12 | 17 | 27 | 43 |
| psl 79 × Z37 | 9,119,760 | 18,239,520 | 35.8 | 38 | 18 | 21 | 28 | 44 |
| pgl 27 × Z463 | 9,100,728 | 18,201,456 | 34.8 | 26 | 21 | 27 | 45 | 68 |
| sl 31 × Z307 | 9,136,320 | 18,272,640 | 36.7 | 29 | 21 | 28 | 42 | 63 |
| sl 37 × Z181 | 9,161,496 | 18,322,992 | 38.1 | 35 | 15 | 30 | 39 | 58 |
| psl 67 × Z61 | 9,171,228 | 18,342,456 | 38.6 | 32 | 15 | 23 | 34 | 52 |
| sl 89 × Z13 | 9,163,440 | 18,326,880 | 38.2 | 89 | 19 | 22 | 30 | 46 |
| sl 29 × Z373 (round 1, failed) | 9,086,280 | 18,172,560 | 34.1 | 29 | 24 | 27 | 39 | 57 |
| psl 263 (round 1, failed) | 9,095,592 | 18,191,184 | 34.6 | 131 | 18 | 21 | 34 | 51 |

Products with a small A5/A4-type factor were not screened (round 1: psl 5 × psl 11 × Z229 was far too costly).

### Runs started (4000 s each, single thread, orbq.sh; queue logs in `runs/raise_d15D8_r2/out/`)

| job | group | μ | flags | seed |
|---|---|---|---|---|
| a | psl 79 × Z37 | 35.8 | ORBW=3 | 5 |
| b | psl 79 × Z37 | 35.8 | plain | 6 |
| c | pgl 27 × Z463 | 34.8 | ORBW=3 | 5 |
| d | sl 31 × Z307 | 36.7 | ORBW=3 | 5 |


### Wave 1 results (4000 s each, 14:34–15:41 UTC; no solve)

| job | group | μ | flags | seed | evals | best cost |
|---|---|---|---|---|---|---|
| b | psl 79 × Z37 | 35.8 | plain | 6 | 1.30·10⁵ | **3** |
| a | psl 79 × Z37 | 35.8 | ORBW=3 | 5 | 1.30·10⁵ | 6 |
| c | pgl 27 × Z463 | 34.8 | ORBW=3 | 5 | 3.5·10⁴ | 7 |
| d | sl 31 × Z307 | 36.7 | ORBW=3 | 5 | 1.0·10⁵ | 9 |

psl 79 × Z37 with plain S reached cost 3 (one uncovered orbit or fixed point) and is the best lead so far.

### Wave 2, first solve: 18,239,520 vertices at (15,8) (psl 79 × Z37, plain S, seed 7)

- Graph: Haar graph of G = PSL(2,79) × Z37, |G| = N = 9,119,760, |S| = 15 = 3·5 (5 free orbits of an order-3 automorphism, f = 0),
  2N = **18,239,520** vertices, 15-regular, 136,796,400 edges, no duplicate edges. μ = 35.8, Fix = 38.
- Found after 121,985 evaluations at 6000 s budget (solved at 3,778 s).
- Verification so far:
  - haar_sym's own full diameter check (direct and s₀ = e normalised): OK.
  - `research/structured/tools/haarcheck_psl` (low-memory PSL checker, orbq.sh): VALID d=15 D=8.
  - build_haar2.py: VALID d=15 D=8, ecc 8 from both sides, 0 unreached, edge-list sha256 `3603a869bf5961200d0d34a4354e6f574d84e4d09d3ea1cf075234103a57f35b` (same as haar_sym's log). `runs/raise_d15D8_r2/verify/psl79_37_s7.build_haar2.txt`.
- **Standing (15,8) record for this branch: 18,239,520.**
- Saved as `research/frontier/sols/d15D8_psl_79_37_orb3f0_s7.txt` (run log `runs/raise_d15D8_r2/out/e/d15D8_psl_79_37_orb3f0_s7.log`).
- Gain over the round-1 bar 18,156,528: +83,000 vertices (+0.46 %).

### Wave 2 results (6000 s each, 15:41–17:21 UTC)

| job | group | μ | seed | evals | best cost |
|---|---|---|---|---|---|
| e | psl 79 × Z37 | 35.8 | 7 | 1.22·10⁵ (solved at 3,778 s) | **0 — solved, 18,239,520** |
| f | psl 79 × Z37 | 35.8 | 8 | 1.90·10⁵ | 3 |
| g | sl 37 × Z181 | 38.1 | 5 | 1.88·10⁵ | 6 |
| h | psl 67 × Z61 | 38.6 | 5 | 1.94·10⁵ | 3 |

### Wave 3 (6000 s each, started 17:21 UTC; all plain S, k = 3, f = 0)

| job | group | N | 2N | μ | seed |
|---|---|---|---|---|---|
| i | psl 67 × Z61 | 9,171,228 | 18,342,456 | 38.6 | 6 |
| j | psl 67 × Z61 | 9,171,228 | 18,342,456 | 38.6 | 7 |
| k | psl 37 × Z361 | 9,136,188 | 18,272,376 | 36.7 | 5 |
| l | psl 31 × Z613 | 9,121,440 | 18,242,880 | 35.9 | 5 |

Every group above has 2N > 18,239,520, so any solve beats the current record.

### Wave 3 result: new record 18,342,456 vertices (psl 67 × Z61, plain S, seed 6)

- Graph: Haar graph of G = PSL(2,67) × Z61, |G| = N = 9,171,228, |S| = 15 = 3·5 (5 free orbits of an order-3 automorphism, f = 0),
  2N = **18,342,456**, 15-regular. μ = 38.6, Fix = 32. Solved after 134,025 evaluations (4,322 s, run i in `runs/raise_d15D8_r2/out/i/`).
- haar_sym full diameter check (direct and s₀ = e): OK. haarcheck_psl: VALID d=15 D=8.
- build_haar2.py: VALID d=15 D=8, ecc 8 from both sides, 0 unreached, edge-list sha256 `14e46c7bcbaae6943e8a65af0367505a0b90708dcb2cb326265b7677fa28c7b5` (`runs/raise_d15D8_r2/verify/psl67_61_s6.build_haar2.txt`).
- Saved as `research/frontier/sols/d15D8_psl_67_61_orb3f0_s6.txt`.
- **Standing (15,8) record for this branch: 18,342,456** (+1.0 % over 18,156,528, +0.6 % over 18,239,520).

Wave 3 runs j (psl 67 × Z61, seed 7), k (psl 37 × Z361) and l (psl 31 × Z613) were stopped at about 4,000 s: any solve from them
has order at most 18,342,456, so it could not beat the new record. Their partial logs stay in `runs/raise_d15D8_r2/out/{j,k,l}/`.

### Final wave 4 (5400 s each, started 18:36 UTC, plain S, k = 3, f = 0)

Groups above the new bar, lowest μ among those screened (tails are weaker than psl 67 × Z61's):

| job | group | N | 2N | μ | seed |
|---|---|---|---|---|---|
| m | sl 25 × Z589 | 9,188,400 | 18,376,800 | 39.6 | 5 |
| n | sl 23 × Z757 | 9,193,008 | 18,386,016 | 39.9 | 5 |
| o | psl 27 × Z937 | 9,208,836 | 18,417,672 | 40.8 | 5 |
| p | psl 31 × Z619 | 9,210,720 | 18,421,440 | 40.9 | 5 |

### Final wave status (19:06 UTC, of 5400 s)

Best costs 15 to 18 for all four (sl 25 × Z589, sl 23 × Z757, psl 27 × Z937, psl 31 × Z619). These are well behind the wave-3 path
(psl 67 × Z61 reached cost 3 before its solve), so a solve before the budget ends (about 20:07 UTC) looks unlikely. The runs are left to finish.

### Final wave result (5400 s each, 18:36–20:06 UTC; no solve)

| job | group | 2N | μ | evals | best cost |
|---|---|---|---|---|---|
| m | sl 25 × Z589 | 18,376,800 | 39.6 | 2.97·10⁵ | 15 |
| n | sl 23 × Z757 | 18,386,016 | 39.9 | 1.08·10⁵ | 18 |
| o | psl 27 × Z937 | 18,417,672 | 40.8 | 1.5·10⁴ | 16 |
| p | psl 31 × Z619 | 18,421,440 | 40.9 | 5.6·10⁴ | 12 |

None of these solved. Their best costs stay well above the psl 67 × Z61 path, so the wall at μ ≈ 40 is out of reach
for these groups in this budget.

### Where this leaves the cell (end of round 2)

- **Record for this branch: 18,342,456** (psl 67 × Z61, seed 6, verified by haar_sym, haarcheck_psl and build_haar2.py).
- Leads not yet exhausted: psl 67 × Z61 at more seeds (one seed of two solved; the other reached cost 3), and the screened
  groups at μ 38–40 with longer budgets. The μ ≈ 40 groups need more than the 5400 s budget here.
- Wave 1–3 runs that were stopped (j, k, l) and the final-wave logs are in `runs/raise_d15D8_r2/out/`.

---

## Round 3 (job "raise3-15-8", Haiku worker, 2026-10-26)

Branch: `claude/raise-d15d8-round3-4sc7rb` (designated branch; based on `claude/raise-d15d8-resume-kwwllj`, round 2).

**Bar to beat: 18,342,456** = 2·|PSL(2,67) × Z61| (round 2, psl 67 × Z61, plain S, seed 6; verified by haar_sym,
haarcheck_psl and build_haar2.py). The brief's 18,128,880 is older: round 1 (18,156,528) and round 2 (18,239,520,
18,342,456) already beat it. Any solve needs N = |G| > 9,171,228. Pending coordinator check on round 2's record.

**Not repeated from round 2:** psl 67 × Z61 (plain and ORBW=3, seeds 6/7 done; same N as the bar, so no new record
possible), psl 79 × Z37, sl 25/23 × Z589/Z757, psl 27 × Z937, psl 31 × Z619, sl 37 × Z181, psl 37 × Z361, psl 31 × Z613,
and everything at k = 3 in the round-1 list.

**What round 1 and 2 never tried:** any orbit type other than k = 3, m = 5, f = 0. STRUCTURE.md (§2.3, §7) argues
that for k = 5 the per-orbit load is μ/5 and the α-fixed misses are |Fix|·e^{−λ/5}, so a k = 5 orbit search can run
at a higher μ than k = 3 (the (11,8) record was solved at μ = 60 with k = 5). Here λ = W/N ≈ 12.4, so
μ ≈ 60 needs N ≈ 9.45 M.

### Screen (orb_screen.py + RANDORB 300 samples, k = 5, m = 3, f = 0; `runs/raise_d15D8_r3/` logs)

| group | N | μ | |Fix| | min | p1 | p10 | median |
|---|---|---|---|---|---|---|---|
| prod psl 9 × psl 9 × Z71 | 9,201,600 | 40.4 | 24 | 10 | 17 | 33 | 56 |
| psl 41 × Z271 | 9,333,240 | 48.7 | 19 | 18 | 29 | 41 | 68 |
| sl 31 × Z311 | 9,255,360 | 43.6 | 29 | 27 | 30 | 46 | 73 |
| pgl 31 × Z311 | 9,255,360 | 43.6 | 29 | 12 | 31 | 47 | 89 |
| sl 61 × Z41 | 9,303,720 | 46.7 | 59 | 22 | 26 | 41 | 64 |

sl 32 × Z281 and pgl 32 × Z281 have no order-5 conjugation (no element of order 5 in SL(2,32)): haar_sym refuses them.

Reference, k = 3 at μ = 38.6 (psl 67 × Z61, the bar, solved): min 15, p1 23, p10 34, median 52.

### Screen (k = 3, m = 5, f = 0, product groups just above the bar; μ ≈ 38.7–40)

| group | N | μ | |Fix| | min | p1 | p10 | median |
|---|---|---|---|---|---|---|---|
| prod psl 7 × psl 25 × Z7 | 9,172,800 | 38.7 | 35 | 19 | 21 | 31 | 49 |
| prod psl 3 × psl 49 × Z13 | 9,172,800 | 38.7 | 71 | 24 | 24 | 37 | 55 |
| prod psl 3 × sl 25 × Z49 | 9,172,800 | 38.7 | 71 | 18 | 27 | 42 | 61 |
| prod psl 3 × psl 17 × Z313 | 9,194,688 | 40.0 | 107 | 39 | 48 | 80 | 154 |
| prod psl 7 × sl 7 × Z163 | 9,201,024 | 40.3 | 17 | 27 | 36 | 51 | 78 |

(prod psl 3 × … has a huge variance in the full cost distribution: the A4 factor mixes badly on some samples.)

### Runs (5400 s each, single thread, `tools/orbq.sh`, `runs/raise_d15D8_r3/out/`)

| job | group | k m f | flags | seed |
|---|---|---|---|---|
| w1a | prod psl 9 × psl 9 × Z71 | 5 3 0 | ORBW=5 | 1 |
| w1b | prod psl 9 × psl 9 × Z71 | 5 3 0 | plain | 2 |
| w2a | prod psl 7 × psl 25 × Z7 | 3 5 0 | ORBW=3 | 1 |
| w2b | prod psl 7 × psl 25 × Z7 | 3 5 0 | plain | 2 |

Status of the wave is below (updated at each checkpoint).

### Wave 1 result: NEW RECORD 18,403,200 vertices at (15,8) (prod psl 9 × psl 9 × Z71, k = 5, m = 3, f = 0, ORBW=5, seed 1)

- Graph: Haar graph of G = PSL(2,9) × PSL(2,9) × Z71, |G| = N = 9,201,600, |S| = 15 = 5·3 (3 free orbits of an order-5
  automorphism, f = 0), 2N = **18,403,200**, 15-regular, 138,024,000 edges, no duplicate edges. μ = 40.4, |Fix(α)| = 24.
  α = conjugation by prod[mat(5,5,7,2); mat(1,5,7,7)] × (z ↦ 5z on Z_71).
- Found after 57,033 evaluations (1,129.6 s, run `runs/raise_d15D8_r3/out/w1a/`).
- Verification: haar_sym's own full diameter check (direct and s₀ = e normalised): OK.
  build_haar2.py: **VALID d=15 D=8**, 18,403,200 vertices, edge-list sha256
  `6f9c1203ad76ebed196a33efbc005ff893e0640d2da2a14beb0ea641d80f639d`.
- Saved as `research/frontier/sols/d15D8_prod_psl_9_psl_9_71_orb5f0_ORBW5_s1.txt` (+ `.log`).
- Gain over the round-2 bar 18,342,456: +60,744 (+0.33 %).
- The wave-1 seed-2 plain run on the same group was stopped (same N, cannot beat this record).

### Wave 1-2 end (no further solve; both k=3 psl 7 × psl 25 × Z7 runs stopped: N = 9,172,800 is below the new bar)

- Wave 2 (k = 3, prod psl 7 × psl 25 × Z7): best cost 6 after about 5.5·10⁴ evaluations, stopped.
- w1b (k = 5, plain, same group as the record): stopped at best cost 1 (same N, cannot beat the record).

### Screen above the new bar (N > 9,201,600; RANDORB 300 samples)

| group | k m f | N | μ | |Fix| | min | p1 | p10 | median |
|---|---|---|---|---|---|---|---|---|
| prod psl 9 × psl 9 × Z71 (record) | 5 3 0 | 9,201,600 | 40.4 | 24 | 10 | 17 | 33 | 56 |
| pgl 31 × Z311 | 5 3 0 | 9,255,360 | 43.6 | 29 | 12 | 31 | 47 | 89 |
| psl 41 × Z271 | 5 3 0 | 9,333,240 | 48.7 | 19 | 18 | 29 | 41 | 68 |
| sl 61 × Z41 | 5 3 0 | 9,303,720 | 46.7 | 59 | 22 | 26 | 41 | 64 |
| prod psl 7 × sl 8 × Z109 | 3 5 0 | 9,229,248 | 42.0 | 26 | 27 | 33 | 45 | 66 |
| prod psl 3 × sl 17 × Z157 | 3 5 0 | 9,224,064 | 41.7 | 53 | 30 | 38 | 54 | 85 |
| prod sl 5 × sl 7 × Z229 | 3 5 0 | 9,233,280 | 42.2 | 35 | 30 | 45 | 63 | 99 |
| prod psl 3 × psl 23 × Z127 | 3 5 0 | 9,253,728 | 43.5 | 35 | 27 | 36 | 54 | 81 |

The record group is still the best-screened of these. The k = 3 product candidates above the bar are all weaker than
the k = 3 bar group was at μ 38.6.

### Wave 3 (5400 s each, started 01:55 UTC; k = 5, m = 3, f = 0)

| job | group | N | μ | flags | seed |
|---|---|---|---|---|---|
| w3a | psl 41 × Z271 | 9,333,240 | 48.7 | ORBW=5 | 1 |
| w3b | sl 61 × Z41 | 9,303,720 | 46.7 | ORBW=5 | 1 |
| w3c | pgl 31 × Z311 | 9,255,360 | 43.6 | ORBW=5 | 1 |
| w3d | psl 41 × Z271 | 9,333,240 | 48.7 | plain | 2 |

Any solve in wave 3 beats the record (18,403,200), since all four groups have N above 9,201,600.
