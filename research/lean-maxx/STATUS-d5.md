# lean-d5: status

Branch claude/d5-formalization-6yt0dm (draft PR #464). Files: lean/BipartiteDD/LeanMaxx/D5/ (new files only). Build one module at a time:
`cd lean && lake build BipartiteDD.LeanMaxx.D5.<Module>`. Axioms of every headline theorem: Axioms.lean / Axioms.out.txt
(propext, Classical.choice, Quot.sound only). No sorry, admit, native_decide.
The cloud container has no toolchain: install elan (github.com/leanprover/elan release tarball), then `lake exe cache get` in lean/.

All statements are about the incidence graph `incGraph P L` of an abstract `GQst P L q q` (elements `P ⊕ L`, colour `col`),
so they hold for every quadrangle; distances are `Reach` (walk of length ≤ n). Notation: D5 = research/theorems/D5_QUADRANGLE.md.

| target | statement | Lean | file | status |
|---|---|---|---|---|
| base | F1, F3 (all pairs ≤ 4, different colours ≤ 3, two neighbours, covering lemma), parity | `GQst.base`, `walk_parity`, `Reach.co_of_two` | Base.lean | done |
| 1 | Theorem A: level graph over any tournament, typing, bijections has diameter ≤ 5; route form (3.1) | `Hyp.repaired_of_empty`, `Hyp.theoremA` | Level.lean, ThmA.lean | done |
| 2 | Theorems 3.5, 3.6: (T') or all arcs repaired, same-colour hubs within 4 ⇒ ediam ≤ 5; Lemma 3.4 | `Hyp.ediam_le_five`, `Hyp.ediam_le_five_of_repaired`, `Hyp.hub_level`, `Hyp.hub_hub` | ThmA.lean | done |
| 2 | order and degree: bipartite, max degree q+1+r, (2r+1)(\|P\|+\|L\|)+\|V\|+\|U\| vertices, hub graph degree ≤ q−r, each freed slot taken at most once; `n_b(q+1+r,5) ≥ (2r+1)·2N + K_A + K_B` | `Surg.degree_le`, `Hyp.colorable`, `Hyp.exists_graph`, `Hyp.exists_graph_N` | Degree.lean, Assemble.lean | done |
| 3 | Theorem E: repaired ⇔ (E2) ∧ (E3), R ≠ ∅ | `Hyp.repaired_iff_E` | ThmE.lean | done |
| 3 | Theorem B: automorphic transition repaired ⇔ freed set pairwise at distance ≠ 2 (partial ovoid/spread); needs the uniqueness half of the GQ axiom (`Strong`, `GQst.strong`) for ⇒ only | `Hyp.repaired_iff_partial`, `Hyp.repaired_of_partial` (⇐, base facts only) | ThmB.lean | done |
| 4 | Corollary 10.3, formal shape: 7 levels HHHDHHD, spread on H→D, partial ovoid on D→H, non-friendly arcs whole (c = 0), complete bipartite hub graph (Y0) | `layout7` (any GQ with a bijection P ≃ L) | Layout7.lean | done |
| 4 | the same for **every odd prime power q**, via the Singer model W(3,q) (SingerC, regular spread; maximal partial ovoid of ≥ q−1 points by counting): for 1 ≤ k ≤ q−3 a bipartite graph of max degree q+4, diameter ≤ 5, 14(q+1)(q²+1)+2k vertices | `SingerC.Setting.family_odd`, `exists_partial_ovoid` | Family.lean | done |

| 3 | Lemma 3.2 / Definition 3.3 for the actual two-level graph `twoLevel D i j`: every vertex of level i within 5 of every vertex of level j ⇔ (3.1) `Data.Repaired`; hence Theorem E in graph form | `Hyp.repaired_iff_reach`, `Hyp.reach_iff_E` | Lemma32.lean | done |
| 3 | Theorem C: (H1) non-collinear freed set, (H3) M(Γ2 x) = Γ2(M x) ⇒ repaired (no (H2) needed at D = 5) | `Hyp.repaired_of_local_dual` | ThmC.lean | done |
| 3+ | Proposition 7.2 as (T'): automorphic arc, relaxed freed set (every element ≤ 1 partner, R1), hub rule (R1h: for partners x, y an 𝓐-hub with slot M y at level j and a slot adjacent to x at level i), three neighbours at every element ⇒ every vertex of level i within 5 of every vertex of level j in X_R^+ | `Hyp.reach_relaxed`, `GQst.base3` | ThmRelaxed.lean | done (Proposition 7.1, the exact bad pairs, not formalised) |

What the family does not do: it uses c = 0 (no two-point local dualities, Theorem C / Proposition 6.4 are not formalised),
the complete bipartite hub graph (k ≤ q−3 per side) and a counting partial ovoid (≥ q−1 points, not the 3q−1 of Lemma 1.3).
The orders are therefore below those of Corollary 10.3 (14N + K_A + K_B with K_B ≤ 6q, K_A ≤ 3q+3) and below the lab's records;
the theorems used are the note's. Not formalised: Proposition 7.1, Proposition 6.1, Corollary 6.2 and Proposition 6.4 (triad centres; existence of two-point local dualities),
Lemma 1.1/1.3/1.4, Proposition 7.1/7.2, Lemma 9.1, Corollaries 10.1, 10.2, 10.4.
