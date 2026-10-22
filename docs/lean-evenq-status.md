# Lean status: H(q) and Theorems D and R for even q (characteristic 2)

Branch `claude/kind-bohr-ofof41`, folder `lean/BipartiteDD/HexagonEven/`. Master files are unchanged except
the import lines added to `lean/BipartiteDD.lean`.

## Target 1: H(q) is a generalized hexagon for every finite field (done)
- `HexagonEven/Plane.lean`: `finrank_plane_all` (`dim π_x = 3` with no characteristic hypothesis). For
  `(2 : F) = 0` it uses the projection `proj6` to `F⁶` (drops the nucleus coordinate `y₃`), injective on
  `π_x` since `Q(e₃) ≠ 0`, with image totally isotropic for the nondegenerate form `B6`.
- `HexagonEven/Through.lean`: `card_lines_through_even` (q+1 lines per point), reusing `card_dc`.
- `HexagonEven/Main.lean`: `genPolygonGraph_hexagon_even [Fintype F] : GenPolygonGraph (incGraph (hexInc (F := F))) 6`.
- `HexagonEven/Sanity.lean`: `hexagon_q2` (ZMod 2, characteristic 2) and `card_spt_q2` (63 points).
- No `sorry`, `admit`, `axiom`, `native_decide` in the proof files. `HexagonEven/Axioms.lean` and
  `Axioms.out.txt`: only `propext`, `Classical.choice`, `Quot.sound`.

## Target 2 (in progress)
- `HexagonEven/Pi.lean`: hyperplane `Π_d : x₀ + x₃ + d x₄ = 0` (`LfunE`, `InPiE`, `SLineE`), with the
  hypothesis `hd : ∀ t, t² + t + d ≠ 0` (replaces `¬ IsSquare (-c)`) and `(2 : F) = 0`. `plane_not_piE`: the
  plane `π_y` of a nonzero singular `y ∈ Π_d` is not inside `Π_d`. Its proof uses a 7×7 certificate
  (determinant `(λ²+λ+d)³` mod 2, found with sympy; `linear_combination` coefficients are in the file).
  `finrank_planePiE` (dim 2), `exists_slineE` (existence), `slineE_unique` (uniqueness of the spread line).
- `HexagonEven/PiCount.lean`: `card_zeros_PiE`, `card_pointsPiE`: `|Π_d ∩ Q| = (q³+1)(q+1)` (elliptic quadric).

## Next
- Target 2: char-2 Hermitian spread in Π (Tr δ = 1), Delorme levels, whiskers (mirror `HexagonD`).
- Target 3: char-2 J_z and key identity, exact whiskers for q ≥ 4, `theoremD_even`, `theoremR_even`.

## Blocker
- None yet.
