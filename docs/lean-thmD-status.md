# Lean status: Theorem D, slice 2 (Hermitian spread, Delorme's levels on H(q), whiskers)

Branch `lean-thmD`, folder `lean/BipartiteDD/HexagonD/`. No `sorry`, `admit`, `axiom`, `native_decide`;
axioms of everything listed below: only `propext`, `Classical.choice`, `Quot.sound` (`HexagonD/Axioms.lean`,
`Axioms.out.txt`). `F` is a finite field with `(2 : F) ≠ 0`, `q = |F|`, `c : F` with `-c` a non-square
(`¬ IsSquare (-c)`; `exists_nonsquare_neg`).

## Done: targets 1, 2, 3

| Brief | Lean |
|---|---|
| Π : x0 + c·x4 = 0, S = H(q)-lines in Π (`SLine c`, `InPi`) | `Pi.lean` |
| Every singular point of Π is on exactly one line of S | `existsUnique_sline`, `exists_sline`, `sline_unique` (key lemma `exists_plane_not_pi`: π_y ⊄ Π, here −c non-square is used; `finrank_planePi`) |
| Distinct lines of S are opposite, distance 6 | `sline_opp`, `sline_edist` (`edist = 6`; generic `opp_iff_edist_eq_six` in `Polygon.lean`) |
| \|Π ∩ Q\| = (q³+1)(q+1), \|S\| = q³+1 | `card_pointsPi` (`PiCount.lean`), `card_sline` (`Spread.lean`) |
| Levels A2 = {v}, A1, A0 and hypotheses (a), (b), ForestDiam 4 | `Levels.lean` (definitions `A0 A1 A2 lev`, structure `Whiskers`), `LevelsHyp.lean` (`lev_ha1`, `lev_ha2`, `lev_hb`, `lev_antitone`), `LevelsForest.lean` (`forestDiam_pi`; abstract `forestDiam_of_rank` in `Forest.lean`) |
| Sizes of the levels | `LevelsCount.lean`: \|A2\| = 1, \|A1\| = q³+q+2, \|A0\| = q⁴+2q³+q²+2q+2+\|W\| |
| Delorme's 1985 bound for odd q (and m-ary) | `delorme_bound_hexagon_two` : n_b(q+2,6) ≥ 2(q+1)(q⁴+q²+1) + q⁴+4q³+q²+4q+10; `delorme_bound_hexagon` for `q+m` |
| Theorem 3 (whiskers) | `whiskers_bound_hexagon`: any `Whiskers c v W` adds `(m−1)·\|W\|`; hypotheses in the report's form: `Whiskers.of_edist` (lines of W not in S, opposite v, i.e. `edist = 6`; no free point = off Π and `edist = 5` from v on two of them) |
| Sanity | `Sanity.lean`: q = 3 gives 948 vertices (degree 5), q = 5 gives 8992 (degree 7) = Delorme's table values |

## Proof outline
1. `Pi`: the plane π_y (dimension 3, `Hexagon.finrank_plane`) meets Π in dimension exactly 2, because the linear form
   `w ↦ L(zvec y w)` is never proportional to `w ↦ B(y,w)` for `y ∈ Π∖0` (the proportionality constant λ would give
   `(c + λ²) y_i = 0`, and `c + λ² ≠ 0` as −c is a non-square). So the unique line through `y` in Π is `π_y ∩ Π`.
2. `Spread`: two lines of S that are joined by a line `M` through points `p ≠ p'` of Π lie in Π (M = ⟨p,p'⟩), hence
   equal by uniqueness. The count is the elliptic quadric count (`hyp` recursion of `Hexagon.QuadricCount`) divided by q−1,
   then divided by the q+1 points per line.
3. `Polygon`: `Opp l₁ l₂` (no point of l₁ collinear with a point of l₂) ⇔ `edist = 6` (walks of length ≤ 4 are case
   analysed); no digons/triangles from the girth 12 (explicit 4- and 6-cycles).
4. `Forest`/`LevelsForest`: in any vertex set A whose points are exactly the singular points of Π and which contains S,
   the rank (S-lines 0, points 1, other lines 2) has at most one lower neighbour (S-lines through a point, Π-point of a
   line not in Π), the root (S-line through the point) is constant on edges, so G[A] is a forest of depth 2.
5. `LevelsHyp`: (a), (b) of `delorme_levelled_polygon`; the whisker condition "no free point on two" is used only for
   points off Π on no line meeting v, and the opposite condition rules out a whisker and a line meeting v through the
   same point.
6. `Delorme`: `delorme_levelled_polygon` with K = 3, the vertex count 2(q+1)(q⁴+q²+1) from `card_spt_eq`, `card_hline`.

## Whole-library build
See the end of this file.
