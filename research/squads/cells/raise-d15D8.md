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

