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
