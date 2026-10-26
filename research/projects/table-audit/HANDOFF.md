# HANDOFF (table-audit)

Round 2 (2026-10-26): branch `claude/table-audit-2-p7x6hn`, draft PR #432 (round 1's branch
`claude/table-audit-1odopy`, PR #316, rebased onto master and continued here). What round 2 added is under
"Round 2" below and in AUDIT.md §7.

Round 1: branch `claude/table-audit-1odopy`, draft PR #316. Read AUDIT.md first. cells.csv, cells.md and the marked parts of
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
  D = 3 AL/FMP cells; (6,7), (8,7) (Delorme 1985 §9); the 15 green D = 5 / D = 7 cells as polygon covers (all 15 pass;
  the (16,7) one, 4,022,340 vertices, took about 2.5 h on 4 shared cores); (3,8) (squad lifts).
- D = 8 green cells: source found (Gómez 1986 thesis, ΩH_q); rebuilt order but diameter 9 with the thesis's labelling
  (checks/omega_D8.txt, tools/omega_bound.py). With a free relabelling of each copy, q = 2 reaches diameter 8
  (tools/omega_anneal.c); for q = 3 annealing stalled at 327 far hub–vertex pairs after 48,444 moves.
- (13,5) ≥ 11,664 (B(H) of Mizuno's (12,4) graph) for the coordinator: AUDIT.md §5.
- Squad rounds table-audit-r1 and r2 logged in research/squads/LOG.md; r2 (all on (3,10) = 800) found nothing at
  800 (closest: symmetric SA with b = 10, c = 80, 8 unreached pairs summed over orbit representatives).
- (3,10) = 800 reproduced at exact order after r2: the r1 c6 annealer (research/squads/table-audit-r1/c6/sym_anneal.c,
  `sym_anneal 10 80 10 2700 11 OUT 6.0 0.1 200000`) found graphs/d3D10_n800_symZ80_b10.edges.txt in 41 min (apsp.c
  VALID, checks/small.txt). tools/sym_anneal2.c (the same plus an exhaustive polish) was used for the 810/820 runs.
- 23 Loz cells reproduced at exact order as metacyclic Haar graphs (graphs/*.sol; checks/small.txt, haar_big.txt,
  haar_huge.txt).

## Running when this was written
Nothing. Every check in checks/ is complete.

## Open
- Whether ΩH_q with some labelling reaches D = 8 at q = 7..13 (the table's (10,8), (11,8), (12,8), (14,8), (16,8);
  (15,8) repeats the (14,8) value).
  A Z₅-symmetric labelling would let apsp_orb-style checks run from one copy per group. Overlaps bigcheck-dist goal 3.
- (13,8) = 15·|H(11)|, (16,5) = 27,300, (3,10) = 800: no source ((3,10) now has a graph of that order).
- (3,10) above 800: tools/sym_anneal2.c at b = 10 reached cost 2 at 810 (7 runs of 45 min) and 4 at 820 (1 run);
  checks/d3D10_beyond800.txt. Longer runs or other (b, c) splits are the next try. Delorme–Gómez 2002 (EJC, open archive; ScienceDirect
  blocks scripts here) and the never-published DGQ paper are the places to look.
- Loz data: try web.archive.org from a machine that can reach it (.../www.eyal.com.au/wiki/The_Degree/Diameter_Problem
  and its bipartite subpage); the thesis (Auckland 2009) is restricted to university logins.
- Big Loz cells (D = 8..10) were not reproduced; (11,10), (15,10), (16,10) are unbeaten and their orders fit
  Z_p ⋊ Z_k Haar graphs (k | p−1), but every element of those groups has order 1, k or p, so haar_gen3's coset bitsets
  give no speed-up there.

## How to rerun everything
- Small cells: `sh tools/rebuild_small.sh /tmp/ta` (a few minutes) rewrites checks/{moore_pg_w,moore_h_small,small}.txt.
- Big cells: commands in checks/CHECKS.md (H(13) all-pairs ≈ 11 min on 4 cores; the (16,7) cover ≈ 1–2 h).

## Round 2 (2026-10-26)

Done:
- D = 8 (Gómez's ΩH_q): `omega/` has the construction with an arbitrary labelling of every copy, an exact evaluator,
  a symmetric annealer, a profiler, an independent wiring check, Singer-type automorphisms of H(q) and the union
  bound. Thesis wiring: witness pair at the (10,8) order (checks/witness_omega7_thesis.txt). Free labelling: ΩH₃ has
  diameter 8 (omega/labs/, checks/omega_labelled.txt). q = 4, 5: not found (lead runs + squad table-audit-2-r1).
  q = 7: random start measured (6.8 million far pairs from 2,064 hub representatives); not searched to the end.
  Verdict in omega/NOTES.md and AUDIT.md §7.
- Literature round 2: lit/LITERATURE2.md, lit/sources2/ (Pérez-Rosés and Feria Purón theses; (13,8) and (16,5) are
  DGQ's unpublished manuscript, not Loz's search; Delorme–Gómez 2002 still not fetched).
- Census check: (3,7) = 168 optimal among vertex-transitive graphs (all bipartite cubic VT graphs on 169–248 vertices
  checked); (3,9) = 506 the largest VT of diameter ≤ 9 (checks/cvt_census.txt, tools/cvt_check.py).
- cells.csv has a `verdict` column (reproduced / reproduced at a different reading / INVALID / no source found).

- Loz cells above 3·10⁶ vertices: exact-order Haar graphs (metacyclic groups) for the remaining cells, checked by
  two or three independent checkers (checks/haar_huge.txt; tools/meta_haar_bits.c, meta_haar_pull.c, the random
  search tools/rand_meta_haar.py and the hill climb tools/meta_haar_climb.c for groups haar_gen3 cannot handle).

Open:
- ΩH_q at q ≥ 4 with some labelling: needs a structured labelling whose routes nearly tile each copy (omega/NOTES.md
  explains the routes). q = 4 is the smallest open case and cheap to evaluate (54,600 vertices, about 15 ms per cost
  with the symmetric sources).
- Delorme–Gómez 2002 (EJC 23, 539–547) from a normal browser: it may contain (13,8), (16,5) and DGQ's D = 8
  constructions. Loz's data via web.archive.org (CDX query in lit/LITERATURE2.md).
