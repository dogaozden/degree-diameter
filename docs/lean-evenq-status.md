# Lean status: even q (characteristic 2), branch `lean-evenq`

Brief: `docs/lean-evenq-brief.md` (on master). Folders: `lean/BipartiteDD/Hexagon/` (edited) and
`lean/BipartiteDD/HexagonEven/` (new). No `sorry`, `admit`, `axiom`, `native_decide` in either folder; axioms
of every checked declaration: only `propext`, `Classical.choice`, `Quot.sound`
(`HexagonEven/Axioms.out.txt`, `Hexagon/Axioms.out.txt`).

## Target 1: H(q) is a generalized hexagon for every finite field — DONE

- The only use of `[NeZero (2 : F)]` in the odd-q hexagon was `Plane.finrank_plane_le` (`dim π_x ≤ 3`), which
  went through `BfForm_nondegenerate`. In characteristic 2 `Bf` is degenerate (radical `⟨e₃⟩`).
- New argument, valid for every field:
  - `Plane.eq_zero_of_Bf_radical`: a singular vector in the radical of `Bf` is zero (`Q(c e₃) = -c²`).
  - `Plane.two_mul_finrank_le_of_ker`: a `Bf`-totally-isotropic subspace `S` with `S ⊓ ker Bf = ⊥` has
    `2 dim S ≤ dim M`, from Mathlib's `LinearMap.BilinForm.finrank_add_finrank_orthogonal'` (no nondegeneracy).
  - `Plane.finrank_plane_le` now uses these; `NeZero (2 : F)` is removed from `Plane`, `Through`, `Main`.
- Result: `Hexagon.genPolygonGraph_hexagon : GenPolygonGraph (incGraph (hexInc (F := F))) 6` now holds for
  every `[Field F] [Fintype F]`. `HexagonEven/Main.lean` records it as `HexagonEven.hexagon_all`.
- `HexagonEven/Sanity.lean`: `H(2)` (characteristic 2), 63 points, 64 singular vectors (`decide +kernel`).
- Build: `lake build BipartiteDD.Hexagon.Main BipartiteDD.Hexagon.Sanity` and `BipartiteDD.HexagonEven.Axioms`
  succeed (on this branch, not the full library).

## Target 2: char-2 Hermitian spread, Delorme levels, whiskers — NOT STARTED

Plan: mirror `HexagonD/` (Pi, PiZ, Spread, Delorme, Levels, Whiskers) with `Tr(δ) = 1` in place of the
`¬IsSquare(-c)` condition. The `HexagonD` modules still carry `[NeZero (2 : F)]`, so they are untouched here.

## Target 3: char-2 J_z, key identity, exact whiskers, theoremD_even, theoremR_even — NOT STARTED

Depends on target 2.
