# table-audit: handoff (Haiku worker, branch claude/table-audit-haiku)

Started 2026-10-25 from origin/master (4b54aa0). No earlier HANDOFF.md existed, and branch `claude/table-audit` does not
exist on origin (only `claude/table-audit-haiku-qxwn2j` and `claude/degree-diameter-table-squad-0xgp3g`), so there was
no earlier session's work to continue. Table source of truth: research/frontier/TABLE.md + heuristic.py TABLE.

## Files
- `inventory.py` -> `cells.csv`: 112 cells (Delta 3..16, D 3..10): table value, Moore bound, status (M = Moore graph,
  opt = proved optimal, open), our best value from the README, beaten yes/no, holder.
- (to come) `moore.py`: Moore-cell builders (PG(2,q), GQ W(q), generalized hexagon H(q)) and their checks.
- (to come) `check_records.py`: edge lists of the repo's record graphs in records/bipartite_dd and their apsp results.
- (to come) `AUDIT.md` / `audit.csv`: final one-row-per-cell table.

## Facts established
- Wiki (combinatoricswiki.org) unreachable from the container again (TLS / HTTP 503). Holders come from the survey
  (TABLE.md "Who holds what") and the README "Where the old records come from". Per-cell colour key NOT read.
- heuristic.py TABLE still has (13,3)=270 and (15,3)=370 (2013 survey); the wiki's 2022 values are 274 and 374 (TABLE.md).
- (11,10) is unreadable in the survey PDF text; no value assumed.
- 27 Moore cells: D in {3,4,6}, Delta in {3,4,5,6,8,9,10,12,14}. 2 proved-optimal cells: (3,5)=56, (7,3)=80.
- 69 cells beaten by our records; 13 open cells not beaten: (6,5) (3,7) (16,7) (4,8) (10,8) (12,8) (14,8) (16,8)
  (3,9) (4,9) (3,10) (15,10) (16,10); plus (11,10) unreadable.

## Next steps (in order)
1. Moore cells: build, apsp.c check (small first), record result.
2. Repo record graphs for beaten cells: convert, apsp check where feasible; large ones via bigcheck-scale runs.
3. Open unbeaten cells: state holder/construction status; attempt only if a construction is traceable.
