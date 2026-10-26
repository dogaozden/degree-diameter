# c15: slot formulas for typed layouts (squad gqd5-r1)

Setting: n = 2r+1 levels, regular tournament T on n vertices (arc u->v = matching transition from u to v),
types H/D per level. Caps: H->D = a, D->H = b, H->H and D->D = c, a >= b >= c >= 0.
K_B = min_v (caps of out-arcs of v), K_A = min_v (caps of in-arcs of v). Objective = max over (T, typing) of K_A + K_B.
Objective is positively homogeneous, so the formulas below are valid on the whole cone a >= b >= c >= 0.
Vertex labels are 0..n-1; "out-lists" give each vertex's out-neighbours. Typing string lists the type of vertex 0..n-1.

## Table per r

| r | levels | best K_A+K_B (formula, a >= b >= c >= 0) | typing | tournament (out-lists) | search coverage |
|---|---|---|---|---|---|
| 1 | 3 | 2c | HHH | 0->2, 1->0, 2->1 (Z3, S={2}) | exhaustive (all 2 labelled) |
| 2 | 5 | 2b+2c (no a) | DHHDH | [[3,4],[0,4],[0,1],[1,2],[2,3]] (Z5, S={3,4}) | exhaustive (all 24 labelled) |
| 3 | 7 | min(a+b+4c, 3b+3c): a+b+4c iff a+c <= 2b, else 3b+3c | HDHHDHH | [[4,5,6],[0,5,6],[0,1,6],[0,1,2],[1,2,3],[2,3,4],[3,4,5]] (Z7, S={4,5,6}) | exhaustive (all 3 iso classes) |
| 4 | 9 | 4b+4c (no a; a-free on every direction probed) | DHDHDHDHH | [[1,2,3,4],[2,3,4,5],[3,4,5,6],[4,5,6,8],[5,6,7,8],[0,6,7,8],[0,1,7,8],[0,1,2,3],[0,1,2,7]] | exhaustive (all 15 iso classes) |
| 5 | 11 | min(2a+2b+6c, 5b+5c): 2a+2b+6c iff 2a+c <= 3b | HDDHHHDDHHH | [[1,2,3,4,5],[2,3,4,5,6],[3,4,5,6,7],[4,5,6,7,8],[5,6,7,8,9],[6,7,8,9,10],[0,7,8,9,10],[0,1,8,9,10],[0,1,2,9,10],[0,1,2,3,10],[0,1,2,3,4]] | partial: 150 of 1213 iso classes (heuristic, lower bound) |
| 6 | 13 | 6b+6c (no a on every direction probed) | DHDDHHDHDDHHH | [[1,2,3,4,5,6],[2,3,4,5,6,7],[3,4,5,6,7,8],[4,5,6,7,8,9],[5,6,7,8,9,10],[6,7,8,9,10,11],[7,8,9,10,11,12],[0,8,9,10,11,12],[0,1,9,10,11,12],[0,1,2,10,11,12],[0,1,2,3,11,12],[0,1,2,3,4,12],[0,1,2,3,4,5]] | partial: 60 reps (circulant + random walk), about 9.7M iso classes exist; heuristic |

Checks: witnesses at the requested points were recomputed from the raw cap definitions (independent script) for r=4 and r=5.
Closed forms for r=3, r=4 and r=5 were compared with the exhaustive or sampled maxima on random directions in the cone
(r=3: 1500 directions, r=4: 300, r=5: 150; max abs error < 1e-6). For r=6, 12 probed directions plus the requested points were checked.

## Requested points (a,b,c) = (q^2+1, q^2-q+1, 2) and (q^2+1, q^2-q+1, 0)

| q | (a,b,c) | r=1 | r=2 | r=3 | r=4 | r=5 | r=6 |
|---|---|---|---|---|---|---|---|
| 9 | (82,73,2) | 4 | 150 | 163 | 300 | 322 | 450 |
| 9 | (82,73,0) | 0 | 146 | 155 | 292 | 310 | 438 |
| 11 | (122,111,2) | 4 | 226 | 241 | 452 | 478 | 678 |
| 11 | (122,111,0) | 0 | 222 | 233 | 444 | 466 | 666 |
| 13 | (170,157,2) | 4 | 318 | 335 | 636 | 666 | 954 |
| 13 | (170,157,0) | 0 | 314 | 327 | 628 | 654 | 942 |

Score line: r=4 at (122,111,2) gives 452 = 4b+4c, from the 15-class exhaustive search.

## Notes
- The a-term appears only for r = 3 and r = 5 (odd r >= 3) and only inside a min() with an a-free branch; for r = 1, 2, 4, 6 the
  best formula is a-free on every direction probed.
- The 9-level search missed one isomorphism class at first (colour-refinement invariant merged two classes); after
  adding a network-x isomorphism split of the buckets, all 15 classes are covered.
- For r=5 and r=6 the candidate tournaments are a sample. Larger K_A+K_B may exist on unsampled classes, so those formulas are lower bounds.
