# HANDOFF (table-audit)

Branch `claude/table-audit-1odopy`. Read AUDIT.md first; cells.csv / cells.md are generated:
`cd tools && python3 audit_results.py [extra.json] && python3 gen_cells.py` (results.json is the source of truth;
extra.json holds results added after the first write, e.g. Haar reproductions).

## Done
- Live wiki table parsed (values, holder colours, upper bounds): lit/wiki_table_2026-10-25.json.
- Literature pass: lit/LITERATURE.md (sub-agent; what is primary vs inferred is marked there).
- Rebuilt and checked: all 27 Moore cells; (3,5), (7,3), (3,7), (4,5), (4,7); all 11 Delorme–Farhi cells; the AL/FMP
  D = 3 cells; (6,7), (8,7) (Delorme §9); the D = 5 and D = 7 green cells as polygon covers. Logs in checks/.
- (13,5) ≥ 11,664 from Mizuno's (12,4) graph (AUDIT.md §5) — for the coordinator.

## Still open / running when this was written
- Exact-order Haar reproductions of Loz cells (tools/exact_haar.py; results appended to an extra.json for
  audit_results.py). Status per cell is in cells.md.
- Squad round table-audit-r1 (research/squads/table-audit-r1/): the five small lost cells (3,8), (3,10), (6,5), (4,8),
  (4,9) by eight other strategies.
- Not attempted: the green D = 8 family (m·|H(q)|, REGULARITIES.md §2.1) — that is bigcheck-dist's goal (3); the big
  Loz cells (D = 8..10, up to 4.1·10⁹ vertices) beyond checking their orders' group shapes; Loz's data (try
  web.archive.org from a machine that can reach it: .../www.eyal.com.au/wiki/The_Degree/Diameter_Problem and the
  bipartite subpage); Delorme–Gómez 2002 (EJC, open archive; ScienceDirect blocks scripts here); Delorme 1985 JGT and
  Bond–Delorme 1988 (not online).

## How to rerun everything
- Small cells: `sh tools/rebuild_small.sh /tmp/ta` (a few minutes) rewrites checks/{moore_pg_w,moore_h_small,small}.txt.
- Big cells: commands in checks/CHECKS.md (H(13) all-pairs ≈ 11 min on 4 cores; the (16,7) cover ≈ 1–2 h).
