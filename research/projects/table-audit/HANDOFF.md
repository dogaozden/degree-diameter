# HANDOFF (table-audit)

Branch `claude/table-audit-1odopy`, draft PR #316. Read AUDIT.md first. cells.csv, cells.md and the marked parts of
AUDIT.md (summary, Loz table) are generated:
`cd tools && python3 collect_extra.py LOZ_NOTES.json RESULTS.jsonl... && python3 audit_results.py ../extra.json &&
python3 gen_cells.py && python3 fill_audit.py` (audit_results.py holds the per-cell text; extra.json adds the Haar
reproductions, which must have a .sol in graphs/ and a VALID line in checks/small.txt or checks/haar_big.txt, and the
Loz group-order notes; a check whose log in checks/ is missing or has no VALID line is printed as PENDING). The
committed extra.json already holds everything found so far, so `python3 audit_results.py ../extra.json && python3
gen_cells.py && python3 fill_audit.py` is enough after a new check log lands.

## Done
- Live wiki table parsed: lit/wiki_table_2026-10-25.json. Literature: lit/LITERATURE.md (+ lead's addendum on
  Gómez's 1986 thesis).
- Rebuilt and checked (logs in checks/): 27 Moore cells; (3,5), (7,3), (3,7), (4,5), (4,7); 11 Delorme–Farhi cells;
  D = 3 AL/FMP cells; (6,7), (8,7) (Delorme 1985 §9); the 15 green D = 5 / D = 7 cells as polygon covers (except
  (16,7), still running below); (3,8) (squad lifts).
- D = 8 green cells: source found (Gómez 1986 thesis, ΩH_q); rebuilt order but diameter 9 with the thesis's labelling
  (checks/omega_D8.txt, tools/omega_bound.py). With a free relabelling of each copy, q = 2 reaches diameter 8
  (tools/omega_anneal.c); for q = 3 annealing stalled at 327 far hub–vertex pairs after 48,444 moves.
- (13,5) ≥ 11,664 (B(H) of Mizuno's (12,4) graph) for the coordinator: AUDIT.md §5.
- Squad rounds table-audit-r1 and r2 logged in research/squads/LOG.md; r2 (all on (3,10) = 800) found nothing at
  800 (closest: symmetric SA with b = 10, c = 80, 8 unreached pairs summed over orbit representatives).
- 23 Loz cells reproduced at exact order as metacyclic Haar graphs (graphs/*.sol; checks/small.txt, haar_big.txt,
  haar_huge.txt).

## Running when this was written (scratchpad, will not survive the session)
- apsp_orb on the (16,7) cover (4,022,340 vertices, 804,468 sources; about 3 h on 4 cores). When the log appears, copy
  it to checks/x7_d16.apsp.txt and rerun the generators; PENDING disappears. If the session ended first, rebuild and
  rerun it from checks/CHECKS.md.
- One 45-min sym_anneal run for (3,10) at b = 10, c = 80 (research/squads/table-audit-r1/c6/sym_anneal.c). A cost-0
  output must still pass apsp.c.

## Open
- Whether ΩH_q with some labelling reaches D = 8 at q = 7..13 (the table's (10,8), (11,8), (12,8), (14,8), (16,8);
  (15,8) repeats the (14,8) value).
  A Z₅-symmetric labelling would let apsp_orb-style checks run from one copy per group. Overlaps bigcheck-dist goal 3.
- (13,8) = 15·|H(11)|, (16,5) = 27,300, (3,10) = 800: no source. Delorme–Gómez 2002 (EJC, open archive; ScienceDirect
  blocks scripts here) and the never-published DGQ paper are the places to look.
- Loz data: try web.archive.org from a machine that can reach it (.../www.eyal.com.au/wiki/The_Degree/Diameter_Problem
  and its bipartite subpage); the thesis (Auckland 2009) is restricted to university logins.
- Big Loz cells (D = 8..10) were not reproduced; (11,10), (15,10), (16,10) are unbeaten and their orders fit
  Z_p ⋊ Z_k Haar graphs (k | p−1), but every element of those groups has order 1, k or p, so haar_gen3's coset bitsets
  give no speed-up there.

## How to rerun everything
- Small cells: `sh tools/rebuild_small.sh /tmp/ta` (a few minutes) rewrites checks/{moore_pg_w,moore_h_small,small}.txt.
- Big cells: commands in checks/CHECKS.md (H(13) all-pairs ≈ 11 min on 4 cores; the (16,7) cover ≈ 1–2 h).
