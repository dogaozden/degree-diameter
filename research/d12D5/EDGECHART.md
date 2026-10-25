# Per-edge route charts over F_3 (cell-12-5, resumed session, 2026-10-25)

## Idea

The route-chart lift (research/theorems/BEAT_16_5_SQUAD.md §2) gives every controller edge the chart letter of its
*colour*: 4 letters (A_c, b_c), c = 0..3. Over F_3 no colour chart has all 216 patterns nonsingular (`universal3.py`).
But nothing in the construction needs colours. If the controller is a voltage lift of a base multigraph, give every
**base edge** e its own letter (A_e, b_e); a controller edge inherits the letter of the base edge it lies over. The lift
is still (a, x)_A ~ (b, A_e x + λ b_e)_B, λ ∈ F_3: bipartite, 12-regular, 2·81·m vertices.

A controller walk is singular iff its projection to the base is, so the 216 colour patterns become the 2·108·k
nonbacktracking base walks of length 4, and the 24 pencil conditions become 12k (one per pair of edges at a base vertex).
With the derivation of BEAT_16_5_SQUAD §2.1 redone for per-edge letters:

- A-side walk e1 e2 e3 e4 (middle A-vertex): nonsingular iff {A_e2⁻¹b_e1, A_e2⁻¹b_e2, A_e3⁻¹b_e3, A_e3⁻¹b_e4} is a basis;
- B-side walk: {A_e2 A_e1⁻¹ b_e1, b_e2, b_e3, A_e3 A_e4⁻¹ b_e4} is a basis;
- pencil for an A-side pair u–a–v through edges e, f at the B-vertex a: Z = {A_e A_k⁻¹b_k : k ≠ e at u} ∪
  {b_l : l at a, l ≠ e, f} ∪ {A_f A_k⁻¹b_k : k ≠ f at v} meets all 4 hyperplanes through ⟨b_e, b_f⟩;
  B side: Z = {A_e⁻¹b_k : k ≠ e at u} ∪ {A_l⁻¹b_l : l at a, l ≠ e, f} ∪ {A_f⁻¹b_k : k ≠ f at v} against ⟨A_e⁻¹b_e, A_f⁻¹b_f⟩.

Per-edge charts are not better *globally* (`echart.c` anneals one alone: 56–72 singular walks of 648 on K33m, about
the colour charts' 8 %). They are better *jointly*: the annealer can make singular exactly the base walks the
controller does not need.

## Tools

- `mlift_ejoint.c`: mlift_joint3.c with per-edge letters (moves: one voltage, or one entry of one A_e / b_e).
  `[INIT_CHART=colour chart | INIT_ECHART=per-edge chart] [INIT_VOLT=v0,..] mlift_ejoint BASE TABLE SECS SEED [T0] [PV] [OUT]`.
- `elift.py CTRL ECHART OUT`: the lift. `emake_builder.py`, `esave_find.sh`: self-contained builder and check file.
- `echart.c`: per-edge chart alone (singular walks + pencil failures).

## Results

| m | base / group | lift | runs | check |
|---|---|---|---|---|
| 66 | K33m / Z_22 | **10,692** | seed 1 of 2, 300 s CPU, started from the 9,720 colour chart | apsp VALID, bfs_all max ecc 5 |
| 75 | K33m / Z_25 | **12,150** | 300 variants of bt3_k33m_0 (csp3.py), VARLIST moves (PV 0.9), 2.4M iterations | apsp VALID, bfs_all max ecc 5 |
| 72 | K33m / Z_24 | 11,664 | same, 189k iterations (and from the m = 72 near miss in 5.8k) | apsp VALID |
| 69 | K33m / Z_23 | **11,178** | backtrack-complete chart diag/bt3_k33m_0 held fixed (DIAGBT=1, PV=1), 154k iterations | apsp VALID, bfs_all max ecc 5 |

The colour-chart annealer (mlift_joint3) had reached m = 60 (1 seed of 5) and cost 4 at m = 66.

## Diagonal pairs for free: backtracking closed walks (14:15 UTC)

A diagonal pair ((u, x), (u, y)) needs y − x in the union of the images of closed walks of length ≤ 4 at u. The
annealers so far only used nonsingular 4-cycles (a closed NB walk whose voltage is trivial), and the last failures are
almost always diagonals (BEAT_16_5_SQUAD.md §2.2). But closed walks that backtrack all have linear part I, and
- u→a→u→b→u (edges e, f at u) reaches x + ⟨c_e, c_f⟩, c_e = A_e⁻¹b_e,
- u→a→w→a→u (e at u, l ≠ e at a) reaches x + ⟨c_e, A_e⁻¹b_l⟩
(A side; B side: x + ⟨b_e, b_f⟩ and x + ⟨b_e, A_e c_l⟩). So if these 6 + 12 = 18 planes cover F_3⁴, every diagonal
pair at u is within distance 4, whatever the controller does. This is a chart-only condition per base vertex
("backtrack-complete"). It cannot hold over F_4 (those 18 lines of PG(3,4) cover at most 4 + 6·3 + 12·4 = 70 < 85 points) but can over F_3
(up to 4 + 6·2 + 12·3 = 52 ≥ 40 points of PG(3,3)). Note the 12 lines ⟨c_e, A_e⁻¹b_l⟩ are the legs of the A-side tripods T_e, so a
vertex whose tripods partition PG(3,3) (all 4-walks through it nonsingular) is automatically backtrack-complete.

`mlift_ejoint2.c` = mlift_ejoint.c + this condition (env DIAGBT=1) + FAKE=1 (all walks, pencils and diagonals good: the
controller ceiling). Fake ceiling on K33m with free diagonals: m = 72 (Z_24) cost 0 in 8,923 iterations and m = 75
(Z_25) cost 0, against cost 2 and 6 when diagonals need 4-cycles.

## No universal per-edge chart over F_3 (14:50 UTC)

All A-walks through an A-vertex y are nonsingular iff the four tripods T_e (e at y) partition PG(3,3). Disjoint tripods
are flat with collinear apexes (tripods.py), and then the partition is forced: the apexes c_e lie on a line l_y and
T_e = (σ_e \ l_y) ∪ {c_e}, where σ_e runs over the 4 planes through l_y. T_e = A_e⁻¹(tripod at b_e in the plane π_w of
the four b's at the B-end w of e), so A_e maps l_y to the fourth line n_{w,e} of π_w through b_e. Hence every B-walk
through w whose two middle edges come from A-perfect vertices has V(e2, e1) = A_e2 l_y2 = n_{w,e2} and
V(e3, e4) = n_{w,e3}, two lines of the plane π_w: they meet, so the walk is singular. Perfect A-vertices make their
B-neighbours' walks singular (and kill the A-pencils), so per-edge charts can only trade singular walks between the
sides, as the annealers find (about 9 % of the 648 walks at best on K33m).

## Backtrack-complete charts by construction (15:00 UTC): research/d12D5/diag/

Annealing never made a chart backtrack-complete (24–38 missing points over the 6 vertices of K33m). A direct
construction works. Gauge: at every base vertex the four apexes (c_e = A_e⁻¹b_e at A-vertices, b_e at B-vertices) are
the frame e_0..e_3. The legs from apex e_i are the lines ⟨e_i, q⟩ for q in a "leg triangle" T_i of the quotient plane
PG(F⁴/e_i), and an edge e from apex i of y to apex j of w is a collineation Ā_e of the quotient planes with
Ā_e(S) = T_j(w) and Ā_e(T_i(y)) = S (S = the frame triangle): B-legs at w are A_e(C_y \ c_e), A-legs at y are
A_e⁻¹(P_w \ b_e). So:
1. `legs.py`: a vertex is complete iff the 6 frame lines and the 12 legs cover PG(3,3); with 98 admissible triangles
   per apex there are exactly 1,920 complete (T_0..T_3) (meet in the middle over coverage masks of the 24 points off
   the frame lines).
2. `csp2.py`: 98×98 triangle compatibility (exists a collineation with the two conditions; 1,652 pairs), then forward
   checking over the base vertices; any lift A_e of Ā_e with A_e e_i = e_j works (the free e_j-row is random).
Every chart found this way has exactly 8 singular 4-walks per base vertex (48 of 648 on K33m, 16 of 216 for the
1-vertex base), no pencil failure and no missing diagonal point, better on all three counts than anything annealed.
Held fixed (PV = 1), it gave m = 69 at once; the joint moves (PV < 1) destroy completeness.

## Chart variants (15:05 UTC)

Which 4-walks are singular depends on the leg triangles (the vertex assignments) AND on which leg goes with which
edge, i.e. on the collineation chosen per edge; the free row of A_e matters for neither. `csp3.py BASE NSOL SEED OUT
NVAR` writes NVAR charts per CSP solution with fresh collineations / free rows. Letters of different variants of the
same solution can be mixed edge by edge without losing backtrack-completeness, so mlift_ejoint2 got a chart move
that does exactly that (env VARLIST = file listing the variant charts). With it: m = 72 and m = 75 at cost 0.

## The ceiling of this construction is the (4,5) bipartite problem (15:30 UTC)

The controller of a route-chart lift must have diameter ≤ 5 (a controller pair at distance d gives lift pairs at
distance ≥ d), so it is a bipartite graph of maximum degree 4 and diameter 5: 2m ≤ n_b(4,5). The best known
(research/frontier/TABLE.md) is 162 vertices, found by this project (research/d5/REPORT.md), and that graph is itself a
Z_27-lift of K_{3,3} plus a doubled matching, i.e. our controller family at m = 81. So m = 81, 13,122 vertices, is the
most this construction can give unless the (4,5) bipartite record is beaten too. Fake-chart (every walk good, free
diagonals) runs find perfect controllers at m = 81 easily (3 of 3 seeds); the real chart must leave, for every controller
pair at distance 4, one nonsingular walk, and on these near-extremal controllers many pairs have very few walks.
Fake ceilings: Z_25 0, Z_26 4, Z_27 0, Z_28 4, Z_29 12 (all with free diagonals).
