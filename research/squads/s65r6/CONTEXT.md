# Squad round s65r6: shared context (read this first)

Job "squad-6-5" (Oct 30, 2026), branch claude/squad-6-5-rounds-ts5nxk, one Opus director + 8 Haiku cards.
Repo root: /home/user/degree-diameter (all paths below are relative to it unless absolute).

## Goal
A bipartite graph with maximum degree 6 and diameter 5 on MORE than 684 vertices (table value 684; Moore bound 1,562).
Each vertex must reach its own colour class by walks of length <= 4 (at most 1 + 6*5 + 6*5*5*5 = 781 non-backtracking
walks) and the other class by walks of length <= 5. At 684 vertices that is 781 walks for 342 targets (2.28 per target).
For comparison the (5,5) record, 384 vertices, runs at 1.78 walks per target: regular voltage lifts of 4-vertex bases
by groups of order 96 = 3 x 32 (few involutions), found by EXACT search, none of them a Haar graph. So (6,5) has room.

## Scorer (the same for every card)
Write your best graph with more than 684 vertices as an edge list (first line n, then one "u v" per line, 0-based) and run

    /home/user/degree-diameter/research/s65/tools/score65 FILE.edges

It prints `SCORE n=.. maxdeg=.. bipartite=.. simple=.. bad=<unordered vertex pairs at distance > 5> diam=..`.
Score = bad (lower is better). bad = 0 with maxdeg <= 6, bipartite, simple, n > 684 is a record candidate: say so
loudly in your reply, and also run `research/s65/tools/apsp FILE.edges 6 5` (prints RESULT VALID/INVALID).
Inside your search use whatever internal cost fits (lift cost = uncovered fibre elements, coset cost, ...); report it
too ("cost"), but always also export your best graph and give its score65 `bad`.
Reference points: a separate run found a 686-vertex graph with bad = 144 and a 685-vertex graph with bad = 165 (both
diameter 6). Adding one vertex to the 684 Haar graph is proved impossible; skip that family.

## Scoreboard
Append exactly ONE line of JSON to /home/user/degree-diameter/research/squads/s65r6/scoreboard.jsonl:

    {"card": "c3", "idea": "<one line>", "code": "<path>", "command": "<exact command that produced the best graph>",
     "n": <vertices>, "score": <bad>, "cost": <internal cost or null>, "valid": true|false,
     "edges": "<path of best .edges>", "next": "<one line: what you would try next>"}

Use `echo '...' >> file` (append, never overwrite). Then reply to the director in at most 5 lines.

## Machine rules (4 cores and 15 GB shared by 9 agents)
- One CPU-heavy process at a time, always `timeout 900 nice -n 10 <cmd>` (or shorter). THREADS=1. At most 1.5 GB RAM.
- No git commands that change anything (no add/commit/push/checkout/stash). Reading with `git show` is fine.
- No edits outside your card folder research/squads/s65r6/<card>/ (create it). Copy a tool into your folder before
  changing it. You may READ anything in the repo.
- Never contact anyone or post anything outside the repo.
- Time box: about 30 minutes wall clock in total. Stop, write the scoreboard line, reply.

## Tools (research/s65/tools/, binaries already compiled next to the sources; read the header comment of each)
- `score65` (scorer), `apsp` (all-pairs check: `apsp FILE 6 5`).
- `vl` (vl.c): annealer over regular voltage lifts of a small bipartite base multigraph by a group.
  `vl BASE GROUP` with env D=5 SECS SEED OUT=sol.txt. BASE format: "b E" / b side bits / E lines "u w [volt]".
  Ready 2+2 bases: research/s65/bases/b22_1.txt ([[1,5],[5,1]]), b22_2.txt ([[2,4],[4,2]]), b22_3.txt ([[3,3],[3,3]]).
  30 s calibration: C11 x Q16 (sg_176_26), base b22_1: lift cost 14 at 704 vertices. Lift cost = number of
  uncovered (vertex, group element) pairs over the base sources; 0 means diameter <= 5.
  `kopt.c`: exact k-opt neighbourhood of a vl solution. `export_lift.py SOL GROUP OUT.edges`: lift -> edge list.
- `b4a2x.c`: EXACT search over all lifts of the 2+2 base [[2,3],[3,2]] at degree 5 (found the (5,5) records): spanning
  tree voltages = 1, the last voltage w solved exactly from the elements the w-free walks miss. Degree 5, |G| <= 128
  as written; read it as the model for semi-exact degree-6 searches.
- `bicay.c`: bipartite bi-Cayley graphs BiCay(G; R, L, S) (2 orbits, each meeting both colours). The director runs
  its exhaustive campaign over all groups of order 344-360: do not repeat it.
- Coset (bi-coset) graphs B(G; H, K): `dcenum.c` (fixed fast annealer, `SA=1 SECS=.. SEED=.. dcenum FILE.dc2 6 5
  OUT.edges`), exporter `sg_export.g` + `dc2_lib.g` (run GAP from research/s65/tools:
  `gap -q -c 'ORDER:=700; H_ORDER:=2; OUTDIR:="dir"; IDS:=[1..36];' sg_export.g`), drivers `sweep.sh`
  (all pairs H, K), `sweep_diag.sh` (H = K only), `sweep_exh.sh` (exhaustive); `dc2_edges.py`. Vertices = 2|G|/|H|.
- `haarex2.c` (+ .g): exhaustive orderly Haar search. `cycgen.c`: Z_n lifts with exact inner voltages.
- Group tables: research/s65/groups/sg/sg_<order>_<id>.txt (+ .name) for orders 115-120 and 172-180 (format: m, then the
  m x m multiplication table, element 0 = identity). More with GAP (installed, full SmallGroups library):
  `cd research/s65/tools && gap -q -c 'ORDER:=184; OUTDIR:="/your/dir";' gap_tables.g`.
  research/s65/groups/bc/bc_<order>_<id>_<k>.txt: groups with an index-2 subgroup, bicay format (bicay_export.g).

Build with `gcc -O3 -march=native -o X X.c -lm`.

## Already ruled out at (6,5) (do not repeat)
- Haar graphs H(G,S): none for 343 <= |G| <= 351 (exhaustive), abelian groups (<= 542 vertices), generalized dihedral
  (<= 524); the best groups (351, 355, C3 x SL(2,5) at 360) stop at cost 2 (one inverse pair missed). 684 itself is the
  Haar graph of C6 x (C19:C3).
- Orbit-symmetric Haar (S invariant under an automorphism of order 2, 3, 5, 6) for all non-abelian groups 343-351.
  Any lift with a symmetry that is transitive on each colour class is a Haar graph: covered above.
- Coset graphs of 29 almost-simple groups (PSL(2,q), PGL(2,q), S6, M10, PGammaL(2,8/9), A7, S7, M11, ...), best cost 13;
  products A5 x S3 x Z3, PSL(2,7) x Z7, SL(2,5) x Z9, A5 x A5, S6 (best 35). |H| = 2 bi-coset anneals: order 688
  (13 runs, best 160), order 720 (193 of 840 groups, H = K, best 16: SmallGroup(720,114)); |H| = 3: orders 1029,
  1032, 1044 (best 30); products C13 x P64, C55 x P16 (bad).
- Lifts: random/simple bases with 7-19 vertices per side (cost grows with size); 2+2 lifts of orders 172-192 by
  annealing (best lift cost 14-15, order 176); 3+3 lifts at 720 by annealing (best 32); 4+4/5+5 lifts (worse).
- Geometry: GQ level graphs give at most 546 at degree 6; building chamber graphs 630 + hubs; polygon lifts; F7^3
  polynomial graphs; AG(3,7) configurations.
- Surgery/edge-swap annealing on the 684 graph and on near misses (686 at 144 bad), structure-free annealing from
  random starts (21,060 bad), Moufang loops, inverse-closed Haar sets.

## New after round s65r1 (research/squads/LOG.md)
- Round 1 bests (internal cost; none valid): tri-Cayley 10 at 690; 2+2 lifts 12-14 at 704 (semi-exact no better than
  plain vl); 3+3 lifts 28 at 696; alpha-invariant 2+2 lifts 38; |H| = 2 coset graphs 6 at 702 (SmallGroup(702,47))
  and 8 at 720 (SmallGroup(720,411), exhaustive optimum 8); near-miss rewiring 1428 bad at 686.
- HAAR GRAPHS IN DISGUISE: in B(G; H, K) with |H| = |K| = h, if a normal subgroup N of index h meets H and K
  trivially, N acts regularly on both sides and the graph is a Haar graph of N. Both round-1 coset hits were of this
  kind (Haar graphs of SmallGroup(351,12) and of C3 x SL(2,5), already excluded exhaustively). Always export with
  `SKIPHAAR:=true;` on the GAP command line (dc2_lib.g then drops every H with a normal complement of index h), e.g.
  `gap -q -c 'ORDER:=704; H_ORDER:=2; OUTDIR:="d"; IDS:=[1..50]; SKIPHAAR:=true;' sg_export.g`. (sweep.sh does not
  pass it: copy sweep.sh into your folder and add `SKIPHAAR:=true;` to its gap -c string.)
- Exporting hundreds of groups in one GAP call is slow: export and sweep in chunks of about 25-50 ids.
- `pkill -f PATTERN` also kills your own shell if PATTERN appears in the command line; use `pkill -f "[d]cenum ..."`
  style patterns, and only kill processes started in YOUR folder (never other cards' jobs).

## New after round s65r2
- Non-Haar coset graphs are far off: |H| = 3 non-Haar pairs exist only at orders 1050/1053 (best cost 150); |H| = 4 at
  orders 4p are all Haar-type; the multi-orbit family "1|2,2" (mcos) plateaus at cost 27 where Haar graphs of the same
  groups reach 6.
- Haar graphs remain closest: exhaustive haarex2 runs this job closed SmallGroup(360, 52..57) (no Haar graph; 360_53,
  55, 56 have sets covering side A, with side B missing 2 or more). 63 low-involution groups of order 352-360 are still
  open: research/s65/haar/list_r3_{0,1,2,3}.txt.
- Lifts: vl + exact 2-opt (kopt K=2) gives VALID (6,5) lifts on 640 vertices (order 160, base [[1,5],[5,1]]);
  at 672 (order 168) the annealer's best (cost 6) is a strict 2-opt local minimum (tools/kdesc.c, exact 2-opt
  descent). Pipeline: research/s65/tools/vk.sh.

## New after round s65r3
- Exhaustive Haar (haarex2): 50 of the 69 low-involution groups of order 352-360 are closed (research/s65/haar/STATUS.md):
  no Haar graph; side-A covers only in 360_53/55/56 (side B then misses >= 2); best side-A miss 1 (352_50).
  Haar annealing over 215 groups with more involutions: best 4 (360_125, 360_136).
- TABU SEARCH BEATS ANNEALING for 2+2 lifts: research/s65/tools/tabu (source research/s65/tabu/tabu.c; header has usage:
  `SECS=.. SEED=.. INIT=random|sol tabu SOL GROUP OUT`, SOL in vl format with identity spanning-tree voltages unless
  INIT=random). 672 vertices: tabu 4 vs annealing 8; 704 (C11 x Q16, base b22_1): tabu 6 vs annealing 12-14.
- Converters (research/s65/tools/): haar2lift.py (Haar graph H(G,S) -> 2+2 lift by an index-2 subgroup N, writes base and
  N's table), bicay2lift.py (bi-Cayley graph -> 2+2 lift by E), normlift.py (re-normalise a lift so the spanning-tree
  voltages are the identity, as tabu/kdesc/kopt expect). Example (cost 4 lift, bad 360, 720 vertices):
  `python3 haar2lift.py ../haar/h360_53/hx_360_53.txt "0 1 19 79 228 282" h.base N.txt && python3 normlift.py h.base N.txt hn.base`.
  Bi-Cayley near miss (cost 4 in bicay units, bad 704): bc_352_141_1 a=3 b=3, S 0 335 258 | R 9 94 339 | L 95 188 220.
- Exact 2-opt (kopt K=2) found no cost-0 neighbour of: the 704 tabu lift (cost 6), the 704 bi-Cayley lift.

## New after round s65r4: the (6,5) analogue of the vertex-transitive (5,5) record
- The vertex-transitive (5,5) graph on 384 vertices is the bi-coset graph B(G; H, H) of G = C3 x SmallGroup(128,139)
  with |H| = 2 (a non-Haar H: inside every index-2 subgroup). CALIBRATION: over the 602 groups P of order 128 with at
  most 11 involutions, G = C3 x P has 231 non-Haar pairs H = K; 4-second anneals give cost 0 for exactly one of them (the
  record) and 12, 30, 34, 44, ... for the rest (median ~56 of 384). The record is a lone outlier found by a sweep.
- The (6,5) analogue: G = C3 x P with P of order 256 (768 vertices, 781 walks for 384 targets per side = 2.03 per
  target, more slack than the (5,5) record's 1.78). First three groups: costs 88-112 of 768 (the same relative level
  as the typical (5,5) groups). 4,284 groups P of order 256 have at most 11 involutions (list
  research/s65/c3p256/ids256.txt, split in part_00..part_05).
- Export tool (run from a folder holding a copy of research/s65/c3p256/c3p_export.g and research/s65/tools/dc2_lib.g):
  `gap -q -c 'PORD:=256; IDS:=[2,3,6]; OUTDIR:="d";' c3p_export.g` writes d/c3p256_<id>_<a>_<b>.dc2 for every pair of
  classes of NON-HAAR core-free subgroups of order 2 (most groups have none: their involutions are central or outside
  the Frattini subgroup). Then `SA=1 SECS=3 SEED=1 timeout 60 nice -n 10 research/s65/tools/dcenum FILE.dc2 6 5 OUT.edges`
  prints "RESULT ... best <cost> vertices 768 ..." (cost 0 = diameter <= 5; OUT.edges is written on improvements).
- Haar exhaustive status: research/s65/haar/STATUS.md plus round-4 tables research/squads/s65r4/c1..c4/; side-A covers
  (side B >= 4 short) also in 360_125, 360_136 and 372_1; nothing valid.

## New after round s65r5
- C3 x P256 (768 vertices), P with <= 11 involutions: about 600+ non-Haar pairs annealed, best cost 48 (median ~100);
  no outlier like the (5,5) record. Groups P with ids above ~26,000 have no non-Haar involution subgroups at all.
- 2+2 lifts by groups of order 192 (768 vertices) under tabu: 22-36 (order 176: 6), dropped.
- Exhaustive Haar status: research/s65/haar/STATUS.md and round-5 card c7's table.
