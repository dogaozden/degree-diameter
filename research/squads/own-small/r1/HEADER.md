# own-small round 1: shared rules for every card (read all of it first)

Job "own-small" (Oct 26 2026). Bipartite degree-diameter problem: find a bipartite graph with maximum degree d and
diameter <= D on MORE vertices than the table. Open cells: (3,10) > 800, (3,9) > 506, (3,7) > 168, (4,8) > 2,184,
(4,9) > 4,970. Bipartite Moore bounds: (3,7) 254, (3,9) 1,022, (3,10) 2,046.

## Machine rules (4 cores and 15 GB shared by ~16 cards and the director)

- Any run longer than ~20 s MUST go through the CPU gate, which waits for a free core and gives you a whole one:
  `$T/slot.sh SECONDS cmd args...`  (SECONDS <= 600 per run; nice and timeout are applied for you).
  Do not run heavy jobs outside the gate, and never more than ONE gated run at a time per card (no `&`).
- Single-threaded programs only. At most 1.5 GB of memory. No git commands that change anything (no add/commit/push).
- Work only in your card folder `research/squads/own-small/r1/<card>/` (absolute path below). Read anything anywhere.
- Time box: about 40 minutes of wall time, about 15 minutes of gated CPU in total. Report before the box ends.

## Tools (T=/home/user/degree-diameter/research/squads/own-small/tools; binaries in $T/bin)

- Edge-list format: first line n, then one "u v" per line (0-based).
- **Scorer (the only one that counts):** `$T/bin/score48 EDGES 3 10` (args: d D). Last line "RESULT VALID n=..." or
  "RESULT INVALID n=... far=<unordered pairs at distance > D> reason=...". Also checks simple/degree/bipartite/connected.
- `$T/bin/flift BASE GROUP d D seconds seed [K] [OUT]`: fast voltage-lift annealer (base <= 64 vertices, bipartite base,
  no loops). `flift BASE GROUP d D eval < VOLTAGES` scores one assignment per line (env LIMIT=c, ONLYLOW=1).
  GROUP = `meta:m:k:r` (Z_m x|_r Z_k) or a binary table `.bin` (int32 N, then N*N uint16, identity 0).
  Cost = number of (base vertex, lift vertex) pairs at distance > D (0 = valid). OUT.edges is the lift edge list.
- `$T/bin/lift`: slower, supports loops, semi-edges ("s"), fixed voltages, ODDSTRIDE (see header of $T/lift.c).
- `$T/bin/salift p GROUPS id seed seconds [T0 T1 out.sol]` (env D=10): anneals the p+p cubic base AND the voltages
  jointly; GROUPS is a text table file from gap_export (see below). `$T/bin/salift2 START.sol ...` starts from a given
  base+voltages (up to 128 base vertices; check its header for the D setting before use). `$T/liftedges.py` turns
  a .sol into an edge list. `$T/requot.py` re-expresses a lift over G as a lift over a subgroup H (bigger base).
- `$T/bin/liftx BASE GROUPS D [id..]`: exhaustive lifts of a small base over every group in a text table file.
- GAP 4 with the SmallGroups library is installed (`gap -q`). Every group of order <= 2000 (except 1024) is available.
  `$T/gap_export_aut.g` exports all groups of an order with Aut(G)-orbit reps; `$T/split_groups.py` makes .bin tables;
  `$T/gap_export.g` writes the text table format salift/liftx read. Put large group files in your card folder's
  `groups/` subfolder (it is not committed).
- Bases: `$T/bases/cubic/` (b22_cubic, k33, heawood, moebius_kantor, pappus, desargues, tutte8, gh2 = Tutte 12-cage),
  `$T/bases/` (quartic: b22_t1, b22_t2, dipole4, k44, ...). Base file: "b m" then m lines "u v".
- Cubic edge-transitive census (sparse6, every graph up to 10,000 vertices): unzip
  /tmp/claude-0/-home-user-degree-diameter/6bbfb942-4016-5a09-834c-7684c0cc81b5/scratchpad/dl/foster/CubicETsparse6.zip
  into your folder (files CAT_n.s6 arc-transitive, CSS_n.s6 semisymmetric; one graph per line). Python decoder:
  networkx is NOT installed; `pip install networkx` is allowed, or write a sparse6 decoder.

## Already found / already ruled out (do NOT redo these)

(3,10), table 800:
- Every cubic vertex-transitive graph up to 1,280 vertices (census): best bipartite with diameter <= 10 is 768. Every cubic
  edge-transitive graph up to 10,000 vertices (Foster census): best 720. So a record must be NOT vertex-transitive.
- 2+2 base lifts (n = 4|G|): EVERY group of order 201..250 is being scanned exhaustively by the director (do not redo).
  Known near miss: SmallGroup(220,2) = Z_11 x| Z_20, n = 880, cost 2 (one orbit of 220 far pairs at distance 11),
  file /home/user/degree-diameter/research/squads/own-small/seeds/nm880_g220_2.edges (proved minimal for 2+2).
- 3+3 base lifts: Z_17 x| Z_8 (order 136, n = 816) exhaustive minimum cost 2 (seed nm816_meta17_8_4.edges);
  meta 7 20 6 min 8; meta 9 16 8 min 12; 8 s anneals on 17 metacyclic/abc groups of order 135..168.
- 4+4 bases x metacyclic groups of order 101..130: best cost 12 (8 s anneals only). 5+5/6+6: never tried at D=10.
- Classic bases (Heawood, Moebius-Kantor, Pappus, Desargues, Tutte 8-cage) x metacyclic/dihedral groups, 20-45 s
  anneals: best Moebius-Kantor x Z_51 (n = 816) cost 46. GH(2)/Tutte 12-cage covers: never seriously tried.
- Cubic Haar graphs (1+1 base) and bipartite Cayley graphs: the director scans every group of order 401..500 (do not redo).
- Bi-Cayley with loops/semi-edges >= 5; non-bipartite bases with parity >= 8; Petersen lifts 16; plain unstructured
  annealing of cubic graphs ~1,900 far pairs at n = 802 (useless); 2-switch repair of an n = 812 near miss: no move.
(3,9), table 506 (a vertex-transitive graph, census CVT(506,9)):
- No cubic VT graph on 508..1,280 vertices has diameter <= 9; no edge-transitive one up to 10,000. 2+2 lifts of
  metacyclic/product groups of order 127..140: min 16; classic bases: Heawood x Z_37 cost 88; 3+3 meta 15 6 4 >= 14.
  Director: 2+2 over every group of order 127..160, Haar over every group of order 254..320 (do not redo).
(3,7), table 168: closed for every graph with a semiregular automorphism group with <= 8 orbits (n = 170..254), all VT and
  edge-transitive graphs; n = 169 needs three perfect degree-2 vertices; 168 is a 2+2 lift over SmallGroup(42,2).
(4,8), table 2,184 (Haar graph of Z_91 x|_25 Z_12): no metacyclic Haar graph of order 1,093..1,130 works (exhaustive);
  no Haar graph of a group with an abelian quotient of order > 216 works (quotient bound); surgery on the 2,184 graph
  floors at 217 far pairs; best Haar near miss n = 2,200 cost 1 (Z_55 x|_2 Z_20); abelian, Cayley, coset, nilpotent,
  orbit-symmetric S and product groups are weak. Director: Haar over every group of order 1,093..1,130 (do not redo).
(4,9), table 4,970 (Haar graph of Z_71 x| Z_35): Z_101 x|_5 Z_25 (n = 5,050) exhaustive minimum cost 2; meta 104 24 7
  (n = 4,992) cost 4, the central involution is always far; PSL/SL/PGL x Z_n best 7; 2+2 lifts 22; 3+3 96; AGL x Z_n 14.

## Scoreboard (one JSON line per card, appended at the end; no essays)

Append exactly one line to /home/user/degree-diameter/research/squads/own-small/r1/scoreboard.jsonl:
{"card": "<id>", "cell": "3,10", "idea": "<one line>", "code": "<path>", "command": "<exact command that produced the
best file>", "n": <vertices>, "cost": <far pairs or lift cost, 0 = valid>, "valid": true|false,
"check": "<score48 RESULT line>", "files": "<best edge list path>", "next": "<one line: what you would try next>"}
Then reply to the director in at most 5 lines. If score48 says VALID with n above the table, say so in line 1.
