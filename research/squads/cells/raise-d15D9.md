# Cell (Δ, D) = (15, 9): raise job raise-15-9 (Haiku worker, branch claude/raise-d15d9-record-sx33j8)

Goal: beat our record 208,029,120 vertices, i.e. a Haar graph with N = |G| ≥ 104,014,561 (vertices 2N). Table value
168,016,334. Current record: SL(2,79) × Z211, N = 104,014,560, 15-regular, diameter 9. File:
research/frontier/sols/d15D9_sl_79_211_orb3f0_s1.txt (orbit search, k = 3, m = 5, f = 0, μ = 24.05, 10,833 evals,
run log research/structured/runs/d15D9_sl_79_211_orb3f0_s1.log).

## Method

- Orbit search `haar_sym`, `ORBIT="3 5 0"` (f = 0: five free α-orbits of size 3, no identity), `THREADS=1`, `K=8`, seed 1,
  2 h per run (`tools/orbq.sh`, one queue per core; 4 queues at a time).
- Choice of group. The useful number is μ_eff = μ/k + 2·|Fix(α)|·e^(−λ/k), λ = ln(N/μ). The factor 2 is for odd D
  (two conditions, see STRUCTURE.md §2.6). The record has μ_eff ≈ 8.98 (μ/3 = 8.02, fixed-point misses 0.96).
  Candidates were taken with μ_eff ≈ 9–10 and N just above 104.01 M.
- Candidate lists: `tools/orb_screen.py 15 9 104014561 106500000 "3 5 0" --list --nmax 2000` (note: the default
  `--nmax 400` hides candidates such as sl 5 × sl 11 × Z661; use --nmax 2000).
- Excluded, with reasons:
  - PSL and PGL factors (involutions; odd D, SIZE_LAW/STRUCTURE §2.6), and SL(2,2^e) (many involutions).
  - Products with SL(2,3) as a factor: haar_sym's automatic α picks −I there, which acts trivially
    (`prod sl 3 sl 49 × Z37` had |Fix| = 1151; killed after a few evals).
  - `prod sl 11 sl 43` with n = 1: |Fix| = 503, μ_eff ≈ 15.6 (killed after 105 evals, cost 28).
  - k = 5 (Δ = 5·3, m = 3, f = 0) on `sl 101 × Z101` (the only SL-type group above our order with elements of order 5
    and small enough N): |Fix| = 99, μ_eff ≈ 14.3; stopped after ~320 evals at cost 56.

## Checkers

- `research/structured/tools/haarcheck_prod.c` (new, this session): independent low-memory check of
  SL(2,p1) × SL(2,p2) × Z_n, p1, p2 prime. It uses dense p⁴ index tables, not the closed-form index of haarcheck_sl.
  Verified: VALID on the two verified product records `research/frontier/sols/d13D8_prod_sl_7_sl_11_7_s101.txt`
  (3,104,640) and `d13D8_prod_sl_7_sl_7_31_orb6swc_s2.txt` (3,499,776); INVALID on a copy with one generator changed.
- SL(2,p) × Z_n: `research/frontier/haarcheck_sl.c` (hcsl) and `haarcheck2.c` (hc2), built into tools/.
- SL(2,q) with q not prime (e.g. sl 49, GF(49)): no low-memory checker yet. Needed before a sl 49 × Z889 result can be saved.

## Runs (status updated as they go)

| job | group | N | μ | μ_eff | |Fix| | started | status |
|---|---|---|---|---|---|---|---|
| j1 | prod sl 5 sl 13 × Z397 | 104,045,760 | 24.17 | 8.95 | 71 | 07:36 | running |
| j2 | prod sl 5 sl 19 × Z127 | 104,241,600 | 24.92 | 9.65 | 107 | 07:36 | running |
| j3 | sl 49 × Z889 (GF(49)) | 104,546,400 | 26.13 | 9.31 | 47 | 07:41 | running; chain: sl 53 × Z703 (μ 26.4), sl 41 × Z1519 (μ 26.5) next |
| j4 | sl 67 × Z349 | 104,942,904 | 27.78 | 10.1 | 65 | 07:36 | running |
| j5 | sl 101 × Z101, k = 5 | 104,050,200 | 24.19 | 14.3 | 99 | 07:45 | stopped (see Excluded) |

Logs: `runs/` (copied on each commit). Working outputs are kept outside the repo until verified.

## Next candidates (SL-only or the cleanest products, μ_eff ≤ ~10, N ≥ 104.01 M)

- sl 47 × Z1009 (μ 26.8, |Fix| ≈ 48), sl 59 × Z511 (μ 27.7), sl 43 × Z1321 (μ 27.9), sl 61 × Z463 (μ 28.3),
  sl 73 × Z271 (μ 29.8, μ_eff ≈ 10.9), sl 113 × Z73 (μ 29.5, μ_eff ≈ 11.3).
- prod sl 5 sl 11 × Z661 (N 104,702,400, μ 26.8, μ_eff ≈ 10.0; |Fix| = 6·12 = 72), prod sl 9 sl 13 × Z67 (μ 29.6).

## Notes for a resumed session

- Verify with `research/structured/tools/haarcheck_prod` (products), `hcsl`/`hc2` (SL×Z), `haarcheck_psl`. Save a
  VALID find to `research/frontier/sols/d15D9_<spec>_orb3f0_s1.txt` and commit the log.
- Do not use `pkill -f` with a job name that appears in your own command line: it kills the shell. Use `ps` + `kill <pid>`.
- Compute scale: about 0.45–0.5 s per eval at N ≈ 1e8 (one core). About 1e4 evals solved μ = 24; μ = 28 needs
  roughly 2–3× more. Each 10× in evals is about +2.6 % in N (SIZE_LAW §4.1, STRUCTURE §6).
