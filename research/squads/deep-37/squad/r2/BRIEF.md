# deep-37 squad round 1: common brief (all cards)

You are a Haiku worker in squad deep-37, round 2 (Opus-led). Cell: bipartite degree-diameter (Delta, D) = (3, 7): find a
bipartite graph with maximum degree 3 and diameter <= 7 on >= 169 vertices (record 168). For cubic bipartite graphs this
means: every two same-side vertices are at distance <= 6.

Working directory: /home/user/degree-diameter/research/squads/deep-37 (cd there first). Your folder:
squad/r2/<card>/ . Write only there, plus lines appended to squad/r2/scoreboard.jsonl. No git commands.

Tools (built; run from the working directory):
- bin/score37 EDGES : one line with far = number of unordered vertex pairs at distance > 7 (0 = candidate).
  Edge-list format: first line n, then one "u v" per line, 0-based.
- bin/apsp EDGES 3 7 : independent all-pairs checker; prints RESULT VALID for a (3,7) graph.
- bin/orbdfs GROUPFILE 7 : exhaustive search for G-invariant cubic bipartite graphs of diameter <= 7 on a G-set. Group
  file: "n order", then `order` lines (each group element as a permutation of 0..n-1), then a line of vertex colours
  (0/1). Env: MAXSOL, SOLPREFIX (writes PREFIX_<i>.edges), PROBE=300 (Knuth tree-size estimate, fast),
  SHARD=i/m SHARDDEPTH=d (split a big tree into m pieces). Validated against brute force; read the header of
  src/orbdfs.c. Speed about 1e5 nodes/s.
- src/gsets.g (GAP): dosets(G, N, OUTDIR, TAG, MAXSETS) writes every admissible G-set of a group G on N vertices
  (stabilisers are {2,3}-groups; colour-preserving, or colour-reversing with an index-2 colour kernel).
  src/gen_gsets.sh ORDER ID N (env OUT=dir) runs it for SmallGroup(ORDER,ID) and writes PROBE estimates to
  OUT/nN/gORDER_ID/est.txt (one line per G-set: file, estimate, orbit description).
- bin/insert BASE 2|3 OUT : exhaustive insertion of a new vertex pair into a cubic bipartite graph (removing 2 or 3
  edges); prints the best far and writes the best graph.
- inputs/c1_base168.edges (C168.1, the record graph), inputs/c1_s170_k2_far46.edges (best known 170: far 46),
  inputs/r3a_best_n170_D5_7_7_far60.edges (far 60, automorphism group F20 with colour-reversing C4),
  inputs/r3b_symbo.c, inputs/r2f_symloc.c, inputs/r2f_mkgroup.py (handsoff-37 engines: symmetric SA / breakout local
  search over G-invariant graphs; same group-file format).
- records/n168_new_girth8_aut168.edges: a second (3,7) graph on 168 vertices found today by orbdfs (girth 8,
  Aut = AGammaL(1,8) = SmallGroup(168,43), vertex orbits 56/28/84).
- src/iso.py FILES... (isomorphism classes via nauty-labelg), src/gutil.py (load, BFS, automorphisms via dreadnaut).
  GAP and nauty are installed.

Known, do not redo: no G-invariant (3,7) graph at 170 for F20 = C5:C4 with colour-reversing C4 (orbit types b = 1..9
settled exactly); C168.1 + one inserted pair: floor far 46 (2-edge) / 48 (3-edge), exhaustive; no colour-preserving
group acting freely with <= 22 orbits; no automorphism of prime order >= 11; above 169 only cubic graphs matter.

Machine rules: 4 cores shared with Opus and 6 other workers. Single-threaded; prefix heavy commands with
`nice -n 15`; at most 1.5 GB RAM. KEEP EVERY COMMAND UNDER 110 SECONDS (wrap with `timeout 100`): longer commands are
moved to the background and you then sit idle. Make long searches chunked/resumable and chain many short runs.
Leave no background processes when you finish.

Time box: about 75 minutes of work (check `date -u` at the start and as you go), then stop.

Scoreboard: append one JSON line per notable result to squad/r2/scoreboard.jsonl:
{"card": "<id>", "idea": "<one line>", "code": "<path>", "command": "<exact>", "score": <number>, "valid": true|false, "next": "<one line>"}
At the end write squad/r2/<card>/NOTES.md (short, plain: what you ran, what came out, numbers) and reply in at most
5 lines. If you find a graph with far = 0 at n >= 169: run bin/apsp on it, save it in your folder, add it to the
scoreboard with valid true, and say so in the first line of your reply.

Round-2 news (Opus, 00:20Z): bin/orbdfs SHARD=i/m was buggy before 00:20Z (shards did not partition the tree); fixed
now, shard totals add up exactly. Round 1 so far: far-46 floor at 170 confirmed by every route (c2); n = 169 best far
122 (c3, insertion into C168.1 + SA) and 123 (c7), both local minima; {2,3}-group families at 170 with few orbits:
1,502 G-sets settled, none (c4).
