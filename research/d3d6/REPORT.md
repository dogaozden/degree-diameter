# Diameters 3 and 6: the AS(q)/copy methods (d3d6-opus, 2026-10-18)

Summary of the agent's final report (main session transcription).

## Record
- (16,3) >= 396 (table 394, Delorme's conic clones). graphs/sym3_q13_d16_n396.json, and an independent second 396,
  graphs/kframe_q13_k3_d16_n396.json; both pass scripts/verify_record.py (graphs/verify_d16D3_n396.txt).
- Construction: PG(2,13) plus three copies of the +2 hat gadget (research/plus2), each on its own anti-flag (point A,
  line l not through A); the three anti-flags are images under the order-3 Singer subgroup (F, F+61, F+122 with
  F = (A=0, l=38, P=38, X=(9,30,120,124))); then a greedy step adds 3 edges between vertices with spare degree.
  Order 366 + 3*10 = 396. Explicit graph checked by computer, not a general theorem.

## Statements
1. Copies cannot beat Delorme at D = 3 (proved by counting): in a projective plane any two points are collinear, so
   point copies with at most a per line total at most a(q+1) - q*w(p); stand-ins do not help (two line copies meet in
   one point and must share its stand-in). PG(2,q) + copies tops out at 394 for q = 13. The AS(q) idea fails at D = 3
   (an exact weighted ovoid gives about Delta^2 vertices, half the Moore bound). At D = 3 the useful extra vertices are
   rewired hat gadgets.
2. Gadget loads (computer-checked): a gadget with m hats (m = 1..4) adds 2m+2 vertices (m = 4 is the +2 rule, m = 3 is
   Araujo-Pardo-Lopez); each raises by one the degree of the points on l and on the lines AX_s and of the lines through
   A and the X_s. At Delta = q+2 only one gadget fits (nothing beyond AL+2 at (11,3), (13,3), (15,3)); at Delta = q+3
   each vertex absorbs two, which gives (16,3).
3. "Theorem C" for hexagons (sketched, computer-checked): Theorem B with stand-ins in both directions keeps diameter 6.
   Built: 910 on H(3) at Delta = 5, 8872 on H(5) at Delta = 7 (passes all checkers; table 8992). Count bound: at most
   1519 extra vertices on H(5) (needs 1180); search reached 1060.

## Ruled out
- A 4th gadget at (16,3) (would give 400-406): no configuration of 4 found (excess stalled at 18/14/9/6 for sizes
  (4,4,4,4)/(4,4,4,3)/(4,4,3,3)/(4,3,3,3); (4,4,4,1) reached excess 2); none of the 780 symmetric triples leaves room
  for a 4th (exhaustive); no twins fit on top of 396.
- (19,3): q = 16 at Delta = q+3 gives at most 546+60, below AL+2 at q = 17 (624). (7,3) = 80 is optimal.
- H(5) minus an elliptic hyperplane section: at most 8820 by degree count. Partial copies in hexagons give distance 7.
  Hexagons of order (q-1, q+1): ruled out by Feit-Higman.
