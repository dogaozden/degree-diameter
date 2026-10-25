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
