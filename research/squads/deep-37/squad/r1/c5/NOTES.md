# c5 (n = 180, 90 vertices per side, delta = 37): exact orbdfs sweeps over G-sets

Run: 23:41-00:40 UTC, Nov 1-2 2026. No far-0 graph found; no solution from any settled G-set (sols = 0 everywhere).

## What was run
- `c5drv.py gen GROUP`: G-sets for SmallGroup(ORDER,ID) on 180 points via `src/gsets.g` (a copy with "skip existing
  file" for resumability: `gsets_resume.g`). Admissible: stabilisers are {2,3}-groups, colour-preserving (k1) or
  colour-reversing with an index-2 kernel (k2).
- `c5drv.py probe GROUP`: `PROBE=300 bin/orbdfs` estimate per G-set, stored in `gs/gGROUP/est.tsv`.
  Sets reported `EXCLUDED_NOT_FAITHFUL` by orbdfs are marked EXCL (the G-action is not faithful, so it is not a
  subgroup of Aut; not searched).
- `c5drv.py solve GROUPS BUDGET`: exact `bin/orbdfs FILE 7` (MAXSOL=50) on every G-set in increasing estimate order,
  across groups in one queue. A set is run unsharded (m=1). If a run exceeds 40 s, the set is split into 8 shards
  (`SHARD=i/m SHARDDEPTH=8`) and the next shard level is tried (up to 256). Every run is in `runs.tsv`.
- Probe estimates are very noisy (sd of the Knuth estimator is about 10x the mean). Several sets with estimate about
  6e3 took more than 90 s, so the estimate is not a reliable cost.

## BUG (reported by coordinator): SHARD=i/m in bin/orbdfs did not partition the tree
- All sharded (m>1) results are void. They were moved to `runs_sharded_pre_fix_ARCHIVED.tsv` (77 rows, all with
  m>1 or HOPELESS) and their sets are not counted as settled.
- Rows in `runs.tsv` with m>1 that were logged after the fix (about 30 rows, TIMEOUT or DONE) are not counted either.
- The score below uses only unsharded (m=1) DONE runs, which the bug did not touch.

## Results (settled = unsharded DONE, sols = 0)

| G-set group (GAP id) | structure | listed | excluded non-faithful | numeric | settled | unsettled | GENDONE |
|---|---|---|---|---|---|---|---|
| (20,1) | C5:C4, central involution | 910 | 501 | 409 | 185 | 224 | yes |
| (20,2) | C20 | 910 | 501 | 409 | 188 | 221 | yes |
| (20,3) | C5:C4 Frobenius (F20) | 910 | 0 | 910 | 435 | 475 | yes |
| (20,4) | D20 | 4891 (partial) | 1350 | 3541 | 1298 | 2243 | NO (gen stopped by time) |
| (30,1) | C5 x S3 | 1301 (partial) | 750 | 551 | 173 | 378 | NO |
| (30,2) | C3 x D10 | 1241 (partial) | 740 | 501 | 153 | 348 | NO |
| total | | 10163 | 3842 | 6321 | **2432** | 3889 | |

Totals: 2432 G-sets settled (0 solutions), 24.6M DONE nodes over all runs (sharded included).
Not started: order 36 (14 groups), order 60 (13), order 120 (34), order 40, order 72. Groups 30_3 and 30_4 not generated.
The partial lists of 20_4, 30_1, 30_2 are a prefix of the G-set list (k1 first); the rest was not generated.

## Notes on the sets
- Stabilisers of order 5 are excluded (order-5 elements must act freely), so only {2,3}-stabilisers appear.
- Excluded non-faithful sets are not subgroups' actions; a graph with a faithful G of this order is covered by
  the faithful G-sets (listed). Nothing about quotient groups was checked.
- Settled counts only cover G-sets we actually completed. Many settled sets have tiny trees (the pruning rejects at
  the root), so the count is a weak measure of coverage.
- Sets not settled: the search trees were too large for the budget (levels up to m = 256 and 40 s per shard).
  No set is marked HOPELESS in the post-fix ledger. Shard-level timeouts are logged as TIMEOUT.

## Files
- `c5drv.py` (driver), `runs.tsv` (post-fix ledger, includes m>1 rows not counted), `runs_sharded_pre_fix_ARCHIVED.tsv`
  (void), `gs/g*/gsets.list`, `gs/g*/est.tsv`, `gsets_resume.g`, `sols/` (empty).
