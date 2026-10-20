# Lean status: Theorem D, slice 2 (Hermitian spread, Delorme's levels on H(q), whiskers)

Branch `lean-thmD`, folder `lean/BipartiteDD/HexagonD/`. No `sorry`, `admit`, `axiom`, `native_decide`;
axioms of everything listed below: only `propext`, `Classical.choice`, `Quot.sound` (`HexagonD/Axioms.lean`,
`Axioms.out.txt`). `F` is a finite field with `(2 : F) ≠ 0`, `q = |F|`, `c : F` with `-c` a non-square
(`¬ IsSquare (-c)`; `exists_nonsquare_neg`).

## Done: targets 1, 2, 3, 4, 5

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


## Target 4: exact whiskers (Theorem 4 of `research/p4/hats/REPORT.md` §4) — done

| Report step | Lean |
|---|---|
| Step 1: Π_z : x0 + c x4 + α x2 + β x5 = 0, S_z is a spread of Π_z ∩ Q, distinct lines opposite | `PiZ.lean`: `exists_plane_not_piZ`, `finrank_planePiZ`, `slineZ_unique`, `slineZ_opp` (the proof of `Pi.lean` for every z) |
| S ∩ S_z = {v} for z ≠ 0 | `Exact.lean`: `vStd = ⟨e1, e6⟩`, `no_second_line` |
| Step 2: a free point has (p2, p5) ≠ 0; through p the lines of S_z, z ∈ A_p | `FreeLines.lean`: `exists_line_meets_vStd` (a singular x with x2 = x5 = 0 is collinear with a point of v, computed directly, no point count), normalisation `u = L(p)⁻¹ p`; `ExactFamily.lean`: `exact_of_family` (π_u ∩ Π_z is 2-dimensional, its Π-vector is unique up to scalar, so lines through u in S_z correspond to z ∈ A_u) |
| Step 3: closed-form identity ν(X(z)) + β³/(α²+cβ²) affine in z along A_p | `ChartA.lean` (u5 ≠ 0), `ChartB.lean` (u5 = 0 ≠ u2): `XA_mem_plane`, `XA_L`, `XA_Lz`, `XA_ne`, `XA_nu`; `XB_*`. All are polynomial identities (`field_simp; ring`) with the explicit vectors of `verify_closed.py`, `verify_closed2.py` |
| Step 4: the cubic G has no zero ⇒ exactly one root | `ExactCharts.lean`: `exact_chartA`, `exact_chartB` (coefficient of s is G(u5, −u2) resp. u2³(1 − c c1)); `GCubic.lean`: `exists_goodCubic` (c0, c1 exist for every finite field with −c non-square; pigeonhole as in the report) |
| W is exact, whiskers, \|W\| = q²(q²−1) | `FreeLines.lean`: `exists_unique_wline`, `wset_whiskers` (`Whiskers c (vS c) (Wset c c0 c1)`); `WCount.lean`: `ncard_notFree` (q²(q+1)), `ncard_free` (q³(q²−1) free points), `ncard_wset` (`\|W\| + q² = q⁴`) |
| Bound | `TheoremD.lean`: `theorem4`, `theoremD`, `theoremD_two`: n_b(q+2,6) ≥ 2(q+1)(q⁴+q²+1) + 2q⁴+4q³+4q+10; `Sanity.lean`: q = 3 gives 1020 vertices (degree 5), q = 5 gives 9592 (degree 7) |

The set is `Wset c c0 c1 = {m ≠ v | ∃ z ≠ 0, m ∈ S_z, ν(m ∩ Π) = F(z)}` with `F(z) = G(z)/(α² + cβ²)`,
`G(a, b) = (c0 a + c1 b)(a² + c b²) − b³`; `ν` is `nuf`, invariant under scaling.


## Target 5: Theorem R (regular graphs of diameter 6) — done

`RegLevels.lean` … `RegHex7.lean`, `TheoremR.lean`. The levelled doubling of the exact hexagon (m ≥ 2) is written as the
bipartite relation `rr` between point versions `VL` and line versions `VR` (`biGraph_rel_eq`, the levelled graph
is the comap of `biGraph rel` along `Equiv.sumSigmaDistrib`), then `Regular.regular_of_twins` is applied:

* sizes: `card_VL_eq`, `card_VR_eq`; `|β| = |α| + (m−1) m (q³ + m − q)`; the lines have the surplus, as in the report;
* pool `P` of deletable line versions (`isP`: a version of a spread line whose last letter is nonzero, `(m−1)(m q³ + m²)`
  elements, `card_pool` with `card_lastne` via `Fin.snocEquiv`), a set `S ⊆ P` of exactly the excess size
  (`exists_deletion`);
* twins: a version in `P` has the twin with last letter `0` (`twin_of_isP`), because over a point of a spread line
  `ℓ` the height drops by one (`hgt_pt_on_sline`), so the neighbourhood does not depend on the last letter;
* degrees: every version keeps at least `q+1` neighbours after deleting any `S ⊆ P` (`degL_ge`, `degR_ge`: pad the
  string of the neighbour with `0`; such a version of a spread line has last letter `0`), so all deficits are at most
  `m−1` (`s = m−1`); the total deficit is at least `(q+1)|S|` (counting the edges to `S`), which exceeds
  `2 s (Δ + s + 1)` (`hbig_arith`);
* `theoremR`, `theoremR_hexagon`, `theoremR_hexagon_two`: a `(q+m)`-regular bipartite graph of diameter at most 6 on
  `2[(q+1)(q⁴+q²+1) + (m−1)((q³+1)(q+1) + m(q+1))]` vertices, `= 2(q+1)(q⁴+q³+q²+4)` for `m = 2`
  (`Sanity.lean`: q = 3 gives 968 vertices (5-regular), q = 5 gives 9348 (7-regular), the values of the report).

`#print axioms` for all main statements: only `propext`, `Classical.choice`, `Quot.sound` (57 lines in
`HexagonD/Axioms.out.txt`; one of them, `biGraph_rel_eq`, uses only `propext`, `Quot.sound`).
