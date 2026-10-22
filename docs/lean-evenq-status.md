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

## Target 2: Hermitian spread in Pi_d, Delorme levels, whiskers (done)
Hyperplane `Pi_d : x0 + x3 + d x4 = 0`, with hypotheses `hd : forall t, t^2 + t + d != 0` (anisotropy, Tr d = 1)
and `hchar : (2 : F) = 0`. Files mirror `HexagonD` (ported mechanically, then fixed):
- `HexagonEven/Pi.lean`: `plane_not_piE` (7x7 certificate, determinant (l^2+l+d)^3 mod 2, found with sympy),
  `finrank_planePiE`, `exists_slineE`, `slineE_unique`.
- `HexagonEven/PiCount.lean`: `card_zeros_PiE`, `card_pointsPiE` (|Pi_d cap Q| = (q^3+1)(q+1)).
- `HexagonEven/Spread.lean`: `slineOfE`, `existsUnique_slineE`, `sline_oppE`, `sline_edistE` (opposite lines),
  `card_slineE` (|S_d| = q^3+1), `ncard_slineE`.
- `HexagonEven/Levels.lean`, `LevelsCount.lean`, `LevelsHyp.lean`, `LevelsForest.lean`: levels A0, A1, A2,
  `Whiskers d v W`, sizes, hypotheses (a), (b) of `delorme_levelled_polygon`, and `forestDiam_pi`.
  Reuses the characteristic-free `HexagonD.Polygon` and `HexagonD.Forest`.
- `HexagonEven/Delorme.lean`: `exists_aniso_even` (char 2: some d with t^2+t+d != 0 for all t),
  `exists_levelled_hexagon`, `delorme_bound_hexagon` (all even q, m >= 1), `delorme_bound_hexagon_two`
  (n_b(q+2,6) >= 2(q+1)(q^4+q^2+1) + q^4 + 4q^3 + q^2 + 4q + 10 for even q), `whiskers_bound_hexagon`,
  `Whiskers.of_edist`.
- `HexagonEven/Main.lean` also has `card_hline_even`.
- Axioms: `HexagonEven/Axioms.lean` and `Axioms.out.txt` list all new results; all use only
  `propext, Classical.choice, Quot.sound`.

## Target 3 (in progress)
- `HexagonEven/Identity.lean`: `JE d α β` (the paper's J_z on Π_z, coordinate 3 fixed by Π_z), `JE_JE` (J² = J + d),
  `Qf_JE`, `Bf_JE`, `tits_JE`, `InPiZE_JE`, `JE_smul`. Every identity is a polynomial identity mod 2; the
  certificates `linear_combination G * h2` were generated with sympy.
- `HexagonEven/JLine.lean`: `isHPair_JE`, `JE_not_mem_span` (uses `hd`), `exists_hline_JE`: `<x, J x>` is a line of
  H(q) in Π_z for a nonzero singular x in Π_z.

## Next
- Target 3: key identity (Lemma key2), G-cubic for q >= 4, the even PiZ/exact whisker set, `theoremD_even`, `theoremR_even`.

## Blocker
- None yet.
