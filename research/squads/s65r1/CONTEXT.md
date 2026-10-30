# Squad round s65r1: shared context (read this first)

Job "squad-6-5" (Oct 30, 2026), branch claude/squad-6-5-bipartite-l3l6dn, Opus director + 8 Haiku cards.

## Goal
A bipartite graph with maximum degree 6 and diameter 5 on MORE than 684 vertices (table value 684; Moore bound 1,562).
Each vertex must reach its own colour class (>= 343 vertices) by walks of length <= 4: there are only 781 such
non-backtracking walks, so the covering is tight (ratio about 2.27).

## Scorer (the same for every card)
Write your best graph with more than 684 vertices as an edge list (first line n, then one "u v" per line, 0-based) and run

    /home/user/degree-diameter/research/s65/tools/score65 FILE.edges

It prints `SCORE n=.. maxdeg=.. bipartite=.. simple=.. bad=<unordered pairs at distance > 5> diam=..`.
Score = bad (lower is better). bad = 0 with maxdeg <= 6, bipartite, simple, n > 684 is a record candidate: say so
loudly in your reply. Inside your search use whatever fast internal cost you like, but the scoreboard number is `bad`.

## Scoreboard
Append exactly ONE line of JSON to /home/user/degree-diameter/research/squads/s65r1/scoreboard.jsonl:

    {"card": "c3", "idea": "<one line>", "code": "<path>", "command": "<exact command that produced the best graph>",
     "n": <vertices>, "score": <bad>, "valid": true|false, "edges": "<path of best .edges>", "next": "<one line>"}

Then reply to the director in at most 5 lines.

## Machine rules (4 cores and 15 GB shared by 9 agents)
- One CPU-heavy process at a time, always `timeout 900 nice -n 10 <cmd>` (or shorter). THREADS=1. At most 1.5 GB RAM.
- No git commands that change anything (no add/commit/push/checkout). No edits outside your card folder
  research/squads/s65r1/<card>/ (create it). You may READ anything in the repo.
- Never contact anyone or post anything outside the repo.
- Time box: about 25 minutes wall clock in total. Stop, write the scoreboard line, reply.

## Tools (research/s65/tools/, compiled binaries next to the sources; read the header comment of each)
- `score65` (scorer), `apsp` (all-pairs check: `apsp FILE 6 5` prints RESULT VALID/INVALID).
- `bicay.c` / `bicay`: bipartite bi-Cayley graphs BiCay(G; R, L, S) of a group G with an index-2 subgroup E whose two
  G-orbits each meet both colours (the (5,5) record on 360 vertices is one: G = S3 x D30). Modes: exhaustive with an
  exact prefilter, annealing, evaluate one graph (SOL=...), write EDGES. The director runs the exhaustive
  campaign over all groups of order 344-360; do not repeat it. Group files for it come from
  `bicay_export.g` (GAP), format: m, multiplication table, parity row, list of automorphisms.
- `vl.c` / `vl`: annealer over regular voltage lifts of a small bipartite base multigraph by a group (multiplication
  table file). `kopt.c`: exact k-opt neighbourhood of a lift. `export_lift.py`: lift -> edge list.
- `b4a2x.c`: EXACT search over all lifts of the 2+2 base [[2,3],[3,2]] at degree 5 (found the (5,5) record): spanning
  tree voltages = 1, last voltage w solved from the missed elements. Only for |G| <= 128 and degree 5 as written.
- `dcenum.c` + `dc2_lib.g` / `dc2_export.g` / `run_group2.sh` / `dc2_edges.py`: coset graphs (bi-coset graphs
  B(G; H, K)) with |H| = |K| = h; exhaustive over unions of double cosets (up to a cap), `SA=1` anneals.
  `scan_nonsplit.g` (+ `bicoset.g`, `bicoset.c`): exporter for non-split involution coset graphs (earlier job).
- `haarex2.c` (+ .g): exhaustive orderly Haar search. `cycgen.c`: Z_n lifts with exact inner voltages.
- `gap_tables.g`: GAP multiplication tables of SmallGroups: `gap -q -c 'ORDER:=60; OUTDIR:="dir";' gap_tables.g`.
- GAP 4.13 is installed (`gap -q`), with the SmallGroups library.
- Pre-made tables: research/s65/groups/sg/sg_<order>_<id>.txt (+ .name) for orders 115-120 and 172-180;
  research/s65/groups/bc/bc_<order>_<id>_<k>.txt (+ .name) for bicay, orders 344-360.

Element 0 is the identity in every table. Build with `gcc -O3 -march=native -o X X.c -lm`.

## Already ruled out at (6,5) (do not repeat)
- Haar graphs H(G,S): none for 343 <= |G| <= 351 (exhaustive), abelian groups (<= 542 vertices), generalized
  dihedral (<= 524); the best groups (351, 355, C3 x SL(2,5) at 360) stop at "cost 2" (one inverse pair missed).
  684 itself is the Haar graph of C6 x (C19:C3).
- Orbit-symmetric Haar (S invariant under an automorphism of order 2, 3, 5, 6) for all non-abelian groups 343-351.
- Coset graphs of 29 almost-simple groups (PSL(2,q), PGL(2,q), S6, M10, PGL(2,9), PGammaL(2,8/9), A7, S7, M11, ...),
  best cost 13; products A5 x S3 x Z3, PSL(2,7) x Z7, SL(2,5) x Z9, A5 x A5, S6 (best 35); 51 of 334 non-split
  involution coset graphs of order 686-720 (best 18).
- Lifts: random/simple bases with 7-19 vertices per side (cost grows with size); 2+2 and 3+3 lifts in 60 s screens
  (best lift cost 24); symmetric lifts whose symmetry is transitive on each side are just Haar graphs; the cost-2 Haar
  optimum of SmallGroup(351,5) written as a 3+3 lift is a strict local minimum.
- Geometry: GQ level graphs give at most 546 at degree 6 (q = 4, r = 1: 510 + hubs); building chamber graphs 630;
  polygon lifts and GH quotients fail by counting; F7^3 algebraic graphs; AG(3,7) configurations.
- Surgery/edge-swap annealing on the 684 graph and on near misses, hubs on the 630 graph, structure-free annealing,
  Moufang loops, inverse-closed Haar sets.
- Bi-Cayley graphs (mixed orbits, the (5,5) record's family): the director's exhaustive campaign over orders 344-360
  is running; early groups (C43 x Q8, C43 x D8, C59 x S3, ...) have no graph surviving even the prefilter.
