# Cell (Δ, D) = (15, 9): raise job raise-15-9, round 2 (branch claude/raise-d15d9-record-r2-0c41x5)

Goal: beat our record 208,029,120 vertices, i.e. a Haar graph with N = |G| ≥ 104,014,561 (2N vertices). Table value
168,016,334. Current record: SL(2,79) × Z211, N = 104,014,560, 15-regular, diameter 9
(research/frontier/sols/d15D9_sl_79_211_orb3f0_s1.txt; orbit search, k = 3, m = 5, f = 0, 10,833 evals).

Any VALID group just above that order is a new record, so the target is N ≥ 104,014,561, not a big jump. Round 1
(branch claude/raise-d15d9-record-sx33j8, notes in research/squads/cells/raise-d15D9.md on that branch and in the
runs/ logs copied here) tried five runs, all cut off around 400 s with cost still above 0; no solution. Its best open
lead was prod SL(2,5) × SL(2,19) × Z127 at cost 14 (697 evals). Round 2 uses 2 h–3 h runs, since the record itself
needed about 10⁴ evals.

## Method (unchanged from round 1)

- `haar_sym` (research/structured/haar_sym.c, built with `gcc -O3 -march=native -fopenmp`), `ORBIT="3 5 0"` (f = 0,
  five free α-orbits of size 3, no identity), `THREADS=1`, K = 8, one process per core, `nice -n 5`.
- Candidates from `tools/orb_screen.py 15 9 104014561 106500000 "3 5 0" --list --nmax 2000`, filtered to admissible
  families: no PSL/PGL factors (involutions, odd D), no characteristic 2 (SL(2,2^e)), no SL(2,3) factor (α = −I
  there, trivial), Z_n with all prime factors ≡ 1 mod 3. Lowest μ among the rest:

  | group | N | μ | |Fix(α)| | notes |
  |---|---|---|---|---|
  | prod SL(2,5) × SL(2,13) × Z397 | 104,045,760 | 24.17 | 71 | round 1 cost 50 at 737 evals |
  | prod SL(2,5) × SL(2,19) × Z127 | 104,241,600 | 24.92 | 107 | round 1 cost 14 at 697 evals (best lead) |
  | SL(2,53) × Z703 | 104,623,272 | 26.45 | 53 | new |
  | SL(2,41) × Z1519 | 104,628,720 | 26.47 | 41 | new |
  | prod SL(2,5) × SL(2,11) × Z661 | 104,702,400 | 26.8 | | next |
  | SL(2,47) × Z1009 | 104,709,984 | 26.8 | | next |
  | SL(2,49) × Z889 (GF(49)) | 104,546,400 | 26.1 | 47 | needs a checker for non-prime q; round 1 cost 48 |

- Verification: `haarcheck_prod` (products), `hcsl` + `hc2` (SL(2,p) × Z_n), `haarcheck_psl` (PSL). A VALID find is
  saved to research/frontier/sols/d15D9_<spec>_orb3f0_s<seed>.txt only after both checks say VALID.

## Round 2, wave 1 (started 14:28 container time, 3 h each, seed 1)

Logs and solution files are in the scratchpad until verified; copies of the logs go to research/structured/runs/.

| job | group | N | μ | |Fix| | status |
|---|---|---|---|---|---|
| w1a | prod SL(2,5) × SL(2,13) × Z397 | 104,045,760 | 24.17 | 71 | running |
| w1b | prod SL(2,5) × SL(2,19) × Z127 | 104,241,600 | 24.92 | 107 | running |
| w1c | SL(2,53) × Z703 | 104,623,272 | 26.45 | 53 | running |
| w1d | SL(2,41) × Z1519 | 104,628,720 | 26.47 | 41 | running |

## Notes for a resumed session

- Each eval is about 0.45–0.5 s at N ≈ 1e8 on one core. 1e4 evals ≈ 1.4 h. Each 10× in evals ≈ +2.6 % in N
  (SIZE_LAW §4.1, STRUCTURE §6), so the reachable μ at a fixed budget only moves slowly.
- Seeds matter: (11,8) failed on seeds 1 and 2 and solved on seed 3 (STRUCTURE §7). A group that stalls at cost
  1–3 for one seed is not necessarily dead.
- Do not use `pkill -f` with a job name in your own command line: it kills the shell. Use `ps` and `kill <pid>`.

## Status, 16:32 UTC (round 2)

| job | group | N | μ | best cost | evals | state |
|---|---|---|---|---|---|---|
| w1a | prod SL(2,5) × SL(2,13) × Z397, seed 1 | 104,045,760 | 24.17 | 20 | 17,225 | running (budget ends ~17:29) |
| w1b | prod SL(2,5) × SL(2,19) × Z127, seed 1 | 104,241,600 | 24.92 | 8 | 17,321 | running, flat since ~14:50 |
| w1c | SL(2,53) × Z703, seed 1 | 104,623,272 | 26.45 | 24 | 14,873 | budget ended, no solution |
| w1d | SL(2,41) × Z1519, seed 1 | 104,628,720 | 26.47 | 42 | 15,689 | budget ended, no solution |
| w2a | prod SL(2,5) × SL(2,19) × Z127, seed 2, RESTART=1 | 104,241,600 | 24.92 | 8 | 8,329 | running (budget ends ~18:14) |
| w2b | prod SL(2,5) × SL(2,19) × Z127, seed 3, RESTART=1 | 104,241,600 | 24.92 | 10 | 8,329 | running (budget ends ~18:14) |

Nothing has reached cost 0 yet. The 5×19×127 group is the most promising (costs 8–10 across seeds), but the
searches stall at 8, the same stall pattern as round 1. The solution files are only written on cost 0; a finished
run without one leaves no .txt. Logs are copied to research/structured/runs/ as raise2_*.log.

## Status, 17:35 UTC (round 2)

- w1a (prod SL(2,5) × SL(2,13) × Z397, seed 1) finished its 3 h budget: best cost 20 after 24,873 evals. No solution.
- w1b (prod SL(2,5) × SL(2,19) × Z127, seed 1) finished: best cost 8 after 25,113 evals. No solution.
- w2a and w2b (same group, RESTART=1, seeds 2 and 3) still running to about 18:14 UTC; best 8 and 10.
- w3a and w3b (same group, ORBW=5 RESTART=1, seeds 4 and 5, 2.5 h each, started 17:35 UTC) are the new attempt. ORBW=5
  makes an uncovered α-fixed element weigh 5 in the annealing energy (STRUCTURE §7 solved (11,8) this way). The best
  costs of the runs so far sit at 8 and 10, which are not multiples of 3, so uncovered fixed elements are the likely
  bottleneck.

Logs are copied to research/structured/runs/ as raise2_*.log.

## Status, 18:05 UTC (round 2)

- w2a (restart, seed 2) and w2b (restart, seed 3) finished their 2.5 h budgets: best 8 and 10. No solution.
- w3a and w3b (ORBW=5 restart, seeds 4 and 5, started 17:35 UTC) still running to about 20:05 UTC; best 12 and 18 so far.
- w3c and w3d (ORBW=5 restart, seeds 6 and 7, started 18:03 UTC, 1.5 h budget) are the two free cores.

Same group throughout (prod SL(2,5) × SL(2,19) × Z127, N = 104,241,600, μ = 24.92, |Fix| = 107). Across seeds
and settings, its best cost has stayed at 8 (a plateau, not a solution). Round 1's cell notes record the same
group at cost 14 after a short run.


## Status, 19:33 UTC (round 2)

- w3c and w3d (ORBW=5 restart, seeds 6 and 7) finished their 1.5 h budgets: best 12 and 12. No solution.
- w3a and w3b (ORBW=5 restart, seeds 4 and 5) still running to about 20:05 UTC. Best 6 each (seed 4 at 6 after about
  8,000 evals; seed 5 at 6). Both wander between 6 and 30 in cost. Nothing has reached cost 0.

Summary of the round so far: on the lowest-μ admissible group (prod SL(2,5) × SL(2,19) × Z127, N = 104,241,600),
best costs across seeds and settings were 8 (plain orbit search, seed 1), 8 (restart, seed 2), 10 (restart, seed 3),
6 (ORBW=5 restart, seeds 4 and 5), 12 (ORBW=5 restart, seeds 6 and 7). Other candidates: 5×13×397 best 20;
SL(2,53)×Z703 best 24; SL(2,41)×Z1519 best 42. No candidate in this round reached cost 0, so the cell is not raised.

Next steps for a resumed session:
- ORBW=5 is the best lever seen so far (it reached 6 where the plain runs stalled at 8). Give it more seeds and
  more budget on 5×19×127 (2 h+ each); the plateau at 6 suggests fixed-point misses are still the bottleneck.
- SL(2,49) × Z889 (μ 26.1) needs a low-memory checker for GF(49) before any find can be saved.
- Round 1 and round 2 both found nothing at N ≈ 1.04e8 in about 3 h per run. The honest read is that this cell
  needs either many more core-hours or a structural change (e.g. a group with a smaller fixed-point set at k = 3).

