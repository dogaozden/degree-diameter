# c6: LPS(3) x Z_m covers, free labels (round thmfam-r2)

Method: LPS(3) generator matrices from gen_lps_cover.py (zero labels), labels set per tuple. WLOG z0 = 0 (shift of all
labels by a constant is an isomorphism) and z1 = a divisor of m (unit multiplication). Exhaustive over z2, z3 in Z_m
(search.py exh) for m up to 40 at q = 5, m up to 26 at q = 7 (m = 1..6 too), m up to 14 at q = 11, m up to 6 at q = 13; haar_ecc run
with -D 10, so only diameter <= 10 FULL covers are seen (diam > 10 cells show as not FULL; they are irrelevant here).

Results (FULL = compA = compB = q(q^2-1)m):
- (4,8): best diameter-8 FULL cover has 1440 vertices (q=5, m=12, z = 0 1 3 10). Table 2184: ratio 0.659.
  Diameter 8 appears only for q=5 with m <= 12 and q=7 with m=1; none above 1440.
- (4,9): best diameter-9 FULL cover has 4368 vertices (q=7, m=13, z = 0 1 3 9). Table 4970: ratio 0.879.
  Diameter 9 vanishes for q=5 at m >= 29 (m=29..39 exhaustive: diameter 10 only) and for q=7 at m >= 14.
- (4,10): best diameter-10 FULL cover has 6720 vertices (q=7, m=20, z = 0 1 2 9). Table 11748: ratio 0.572.
  Lab record 12416 not approached.
- No FULL graph beats 2184 at diameter <= 8 or 4970 at diameter <= 9, so no new record claim.

Checks: the three best covers were re-checked with verify_cover.py (independent Python BFS: diameter 8, 9, 10) and with
component_edges.py + apsp (VALID at D = 8, 9, 10; n = 1440, 4368, 6720; 4-regular, bipartite).

Reproduce: python3 /home/user/degree-diameter/research/theorems/haar_families/gen_lps_cover.py 3 7 13 free 0 1 3 9 \
  | /home/user/degree-diameter/research/theorems/haar_families/haar_ecc pgl 7 13
Search driver: research/squads/thmfam-r2/c6/search.py (q m exh|rnd budget seed). Logs: scan_*.jsonl.
Open: m >= 41 at q = 5 for diameter 9 (would need V > 4970) was not scanned exhaustively; random sampling gave only
diameter-10 FULL covers there (1 hit each at m = 41, 42).
