# d10D7 squad round 4: bigger partial ovoids and spreads = more hub vertices

**The construction (proved and apsp-checked, research/d10D7/checks/B2_hubs_CHECK.md).** In the record graphs X(M)
over the generalized hexagon H(q), freeing a pair (p, l) adds 2 vertices. It needs only that M maps the q(q+1)
points at distance 2 from p onto the q(q+1) lines at distance 2 from l. So the number of freed pairs K is limited
only by how many pairs can carry this structure at once:
- (10,7) [q = 8], (9,7) [q = 7], (7,7) [q = 5]: K = min(|P|, |L|), where P is a set of **pairwise opposite points**
  (a partial ovoid: every two at distance 6) and L a set of **pairwise opposite lines** (a partial spread).
  Greedy random gives |P|, |L| = 67, 68 at q = 8 (→ 224,828), 56, 57 at q = 7 (→ 117,760), 39, 32 at q = 5
  (→ 23,500). Every extra pair is +2 vertices.
- (11,7) [q = 9, Δ = 11] and (12,7) [q = 9, Δ = 12]: H(9) is self-dual, so M can be a duality and any set of
  **pairwise non-collinear points** works (no two on a common line). Greedy random: 2,821 (→ 404,222 and 675,584,
  being checked). The Hoffman bound is N/10 = 6,643 (a distance-2 ovoid, one point on every line).

Facts you can use. H(q) = points of the parabolic quadric Q(6,q): X0X4 + X1X5 + X2X6 = X3^2, with lines chosen by
Tits' equations (research/d10D7/hexgen2.c). **Two points are opposite in H(q) iff they are non-collinear on Q(6,q)**,
i.e. B(x,y) != 0 with B the polar form (in characteristic 2 the X3 term drops out: B(x,y) = x0y4 + x4y0 + x1y5 + x5y1
+ x2y6 + x6y2). So partial ovoids of H(q) = partial ovoids of Q(6,q). Known: Q(6,q) has ovoids (q^3+1 points) only
for q = 3^h; an ovoid of a Q(4,q) section (an elliptic quadric, q^2+1 points) gives q^2+1 pairwise opposite points.
Lines of H(q) are opposite iff at distance 6 in the incidence graph.

## Tools
- Hexagons: `research/d10D7/hex/hex_q{2,3,4,5,7,8,9}.bin` (int32 q, N, N; then N*(q+1) int32 point ids per line;
  then N*7 uint8 point coordinates, GF(q) element = a0 + p*a1 + p^2*a2 in the polynomial basis of hexgen2.c).
- Scorer (the only thing that counts): `research/squads/d10D7-r4/tools/setcheck HEXBIN FILE points|lines
  opposite|noncollinear` → "VALID size S". FILE = whitespace-separated ids.
- Python helpers: research/squads/d10D7-r3/tools/hexkit.py (Hex(q).bfs, opposite, ...).
- Opus will turn your sets into graphs with `d7hex b2` (B2PTS=points.txt B2LINES=lines.txt) and check with apsp.

## Rules
4 cores and 15 GB shared by Opus and the cards. Heavy commands: `timeout <=1500 nice -n 10 ...`, one process at a time,
< 1.5 GB RAM. Work only in `research/squads/d10D7-r4/<card>/`, no git commits. Save your best set(s) as plain id
files in your folder. Append ONE JSON line to `research/squads/d10D7-r4/scoreboard.jsonl`:
`{"card": "cN", "idea": "<one line>", "code": "<path>", "file": "<path of best set>", "command": "<exact>", "score":
<size>, "metric": "<what>", "valid": true|false, "next": "<one line>"}` and reply in at most 5 lines.
