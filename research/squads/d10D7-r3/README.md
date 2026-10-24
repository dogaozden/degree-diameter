# d10D7 squad round 3: more vertices at (Δ, D) = (10, 7)

Goal: beat our (10,7) record **224,718** (table 224,694 = 3·|H(8)|; bipartite Moore bound 1,195,742).

## The construction we have (read research/squads/exp2/hexd7/README.md first, 5 minutes)

X(M): three copies (levels 0,1,2) of the incidence graph of the generalized hexagon H(q); point p at level i gets one
extra edge to the line M(p) at level i+1 (M any bijection points -> lines). Degree q+2, diameter 7 for every M.
For (10,7), q = 8 and there are 3·74,898 = 224,694 vertices.

Hubs: free a flag (p, l = M(p)), i.e. delete the 3 extra edges of p, and add 2 vertices: z ~ (p,0),(p,1),(p,2) and
z' ~ (l,0),(l,1),(l,2). That gives +2 vertices per freed pair. The graph keeps diameter 7 iff (p,0) still reaches
every point opposite p at level 1 within 6 ("side A") and (l,0) every line opposite l at level −1 ("side B"). These
need routes through other points' extra edges:
- type 4: u at distance 4 from p, M(u) at distance 5 from p, x on M(u);
- type 2: u at distance 2 from p, x within distance 3 of M(u);
- hub-graph links: z_j ~ z'_k gives side A of pair j the 3-ball of l_k.
Same-side hubs must be within distance 6 of each other: either hub-graph distance ≤ 4 or freed points within
hexagon distance 4.

**New in this session (Opus): the joint algebraic cover.** For one pair, any M that maps S'(p) (the points at
distance 4 from p, not via l) onto S(l) covers both sides exactly. For K pairwise opposite flags, give each point u
the membership vector (bit k set iff u ∈ S'(p_k)) and each line L the vector (bit k iff L ∈ S(l_k)). An M mapping
every point to a line with the SAME vector covers all K pairs at once. The vector counts agree exactly for K = 3.
The mismatch (Σ_v |#points(v) − #lines(v)|) grows with K: about 3,000 at K = 12, 15,000 at K = 21 and 57,000 at K = 40.
With 12 pairs the leftover defects are repaired by the proxy search in about 90 s, giving 224,718 (apsp VALID). A
growth mode then adds pairs one at a time. So the question now is how many pairs can be carried.

## Tools (already built; do NOT rebuild into research/d10D7, copy into your card folder if you change code)

- Hexagons: `research/d10D7/hex/hex_q{2,3,4,5,7,8}.bin` (int32 q, N, N, then N·(q+1) point ids per line).
- `research/squads/d10D7-r3/tools/hexkit.py`: Python (numpy) helpers: Hex(q), bfs, random_opposite_flags, mismatch,
  joint_cover, uncovered (type-4 / type-2 / hub-link coverage per pair). Read its docstring.
- `research/d10D7/d7hex` (source research/d10D7/d7hex.c, header documents every option). Typical search:
  `OPPFLAGS=1 SKIPFULL=1 ./d7hex search research/d10D7/hex/hex_q8.bin K SEED SEC OUT.sol 3 4 4 HUBGRAPH.txt`
  (mode 3 = hub graph from file, alg 4 = joint cover; GROW=Kmax STEPSEC=s NCAND=c HGDEG=d MAXFAIL=f add pairs one at a
  time after the first solve and write OUT.sol.K<k> checkpoints). Hub graphs: `python3 research/d10D7/mkhub.py rnd K d seed out.txt`.
- Checker (the only thing that counts): `research/d10D7/d7hex edges HEXBIN SOL out.edges` then
  `research/d10D7/apsp out.edges Δ 7` → must print `RESULT VALID`. q = 8: Δ = 10, about 100 s and 300 MB.
  q = 5: Δ = 7 (cell (7,7), our record 23,488 = K 26), seconds. q = 7: Δ = 9 (cell (9,7), record 117,690 = K 21).

## Machine rules

4 cores and 15 GB shared by Opus and 8 cards. Every heavy command: `timeout <=1800 nice -n 10 ...`, one process at a
time per card, at most about 1.5 GB of memory. No git commits, no edits outside your card folder
`research/squads/d10D7-r3/<card>/`. Write sols/edges only inside your folder (edge lists for q = 8 are 20 MB: delete
them after checking).

## Scoreboard

Append ONE line of JSON to `research/squads/d10D7-r3/scoreboard.jsonl`:
`{"card": "cN", "idea": "<one line>", "code": "<path>", "command": "<exact>", "score": <number>, "metric": "<what the
number is>", "valid": true|false, "next": "<one line>"}` and reply to Opus in at most 5 lines.
