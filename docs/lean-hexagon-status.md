# Lean status: the split Cayley hexagon H(q) (Theorem D, slice 1)

Branch `lean-hexagon`, folder `lean/BipartiteDD/Hexagon/`. All three targets of `docs/lean-hexagon-brief.md`
are done, including the stretch goal. No `sorry`, `admit`, `axiom`, `native_decide` anywhere in the folder;
axioms: only `propext`, `Classical.choice`, `Quot.sound` (`Hexagon/Axioms.lean`, `Axioms.out.txt`).

## Main results (F a finite field with `(2 : F) ≠ 0`, i.e. `[Fintype F] [NeZero (2 : F)]`, `q = |F|`)
- `Defs`: `Qf x = x0x4 + x1x5 + x2x6 - x3²`, `Bf`, Tits' six equations `Tits x y` (exactly those of
  `research/gh6/gh_build.py`), `IsHPair x y`, `SPt F` (singular points), `HLine F` (2-dim subspaces all of
  whose pairs satisfy `IsHPair`).
- `QuadricCount`: `card_zeros_Qf` (`q⁶` zeros in `F⁷`, any field), `card_spt_eq`
  (`Nat.card (SPt F) = (q+1)(1+q²+q⁴) = (q⁶-1)/(q-1)`).
- `Local`/`Through`: `card_points_hline` (`q+1` points per line), `card_lines_through` (`q+1` lines per point),
  `card_hline` (as many lines as points).
- `Main`: `genPolygonGraph_hexagon : GenPolygonGraph (incGraph hexInc) 6` (girth 12, diameter 6).
- `Sanity`: instances for `ZMod 3`, `ZMod 5`, point counts 364 and 3906, and the `q = 3` zero count by
  `decide +kernel`.

## Proof outline (so the next slice can reuse it)
1. `Zorn`: the split octonions as `Fin 8 → F`; `φ : F⁷ → C8` is the trace-zero embedding with `N ∘ φ = Qf`.
   With the sign choice `φ x = (x3, -x3; -(x0,x1,x2), (x4,x5,x6))` the six vector components of `φ x · φ y`
   are the six Tits equations and the scalar parts sum to `-Bf`. All algebra identities are `ring`.
2. `Lines.isHPair_iff`: `IsHPair x y ↔ Qf x = 0 ∧ Qf y = 0 ∧ φ x · φ y = 0` (the scalar part vanishes because
   `x (x y) = x² y = 0`).
3. `Plane`: `π_x = ker (y ↦ φx·φy)` has dimension exactly 3 (upper bound: totally singular in the 7-dim
   `Bf`-space; lower bound: the image is totally singular in the 8-dim `Bn`-space, rank-nullity).
4. `Through`: double counting the `q²+q+1` points of `π_x` gives `q+1` lines through `x`.
5. `Moore.genPolygonGraph_six`: abstract theorem: a finite incidence structure with `q+1` lines per point and
   points per line, `(q+1)(1+q²+q⁴)` points, and every point joined to every line by a walk of length ≤ 5, has
   `GenPolygonGraph 6` (non-backtracking walk counting: the map from walks of length 1, 3, 5 to lines is onto
   an equally large set, hence injective, which excludes cycles of length < 12).
6. `Main.exists_walk`: for a point `x` and line `W`, pick `w ∈ W` with `Bf x w = 0` (a linear form on the
   2-dim `W`), and `z = φ⁻¹(φx·φw)`: then `x – z – w` are pairwise collinear, giving a walk of length 5.

## Left for later slices
- Nothing from this slice. Possible follow-ups for Theorem D: the hat/whisker sets and the levelled-doubling
  hypotheses (`Doubling.delorme_levelled_polygon`) for H(q), now that `GenPolygonGraph (incGraph hexInc) 6`
  is available.
- Remark: the odd-characteristic assumption is used only for `Bf` being nondegenerate (`dim π_x ≤ 3`).
