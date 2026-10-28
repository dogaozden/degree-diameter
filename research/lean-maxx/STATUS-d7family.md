# STATUS: lean-d7family (n_b(q+2, 7) >= 6N(q) + 2(q^2+1))

Branch `claude/d7-family-diameter-formalize-sqtpmv`, built on lean-all (claude/lean-all-jvj7b0) by a merge.
Files: `lean/BipartiteDD/LeanMaxx/D7Family/`. Build with `lake build BipartiteDD.LeanMaxx.D7Family.<Module>`.

## Done (builds, standard axioms only, no sorry)

- `Hub.lean`: the hub graph. A tree on `Node d m ⊕ Node d m`, degree <= d+1, same-side distance <= 6,
  `1 + d + d^2 + m` nodes per side (`reach_VV`, `reach_UU`, `card_NS_left`, `card_NS_right`, `exists_par`).
  With `d = q-2`, `m = 3d+4` it has `q^2+1` hubs per side and degree `q-1` (for `q >= 5`).
- `Assembly.lean`: `d7_of_sets`. For any finite field `F`, `q = |F| >= 5`, a set `R` of `q^2+1` points of
  `H(q)` with pairwise non-orthogonal representatives (`Bf r s ≠ 0`) and a set `S` of `q^2+1` pairwise opposite
  lines gives `∃ G : SimpleGraph (Fin (6N + 2(q^2+1))), IsBipartiteDegDiam G (q+2) 7`.
  Uses `HexagonD7.exists_graph`, `exists_local_duality`, the plane lemma `Bf_eq_zero_of_mem_plane` (the (F4)
  direction needed, valid in every characteristic).

- `Odd.lean`: `d7_odd`. For every finite field `F` of odd characteristic with `q = |F| >= 5`:
  `∃ G : SimpleGraph (Fin (6 * ((q+1)*(1+q^2+q^4)) + 2*(q^2+1))), IsBipartiteDegDiam G (q+2) 7`.
  Points: the elliptic quadric `(1, x, 0, y, y^2 - a x^2, a x, 0)`, `e_4` (`a` a non-square), pairwise `Bf = (y-y')^2 - a (x-x')^2 ≠ 0`.
  Lines: `q^2+1` of the `q^3+1` lines of the Hermitian spread `SLine (-a)` (HexagonD/Spread.lean).
- `Main.lean`: `d7_family_odd`. For every odd prime power `q >= 5` (`IsPrimePow q`, `Odd q`):
  `∃ G : SimpleGraph (Fin (6 * ((q^6 - 1)/(q - 1)) + 2*(q^2+1))), IsBipartiteDegDiam G (q+2) 7`,
  via the Galois field of order `q`.
- `Even.lean`: `d7_even`. Same for a finite field of characteristic 2 with `q >= 5`. Points: the elliptic quadric
  `(1, x, 0, x + b y, (x + b y)^2 - x y, y, 0)`, `e_4` with `t^2 + t + b^2 ≠ 0` for all `t` (`exists_beta`),
  pairwise `Bf = (Δx + b Δy)^2 - Δx Δy ≠ 0`. Lines: `q^2+1` of the `q^3+1` lines of `SLineE (b^2)`
  (HexagonEven/Spread.lean).
- `Main.lean`: `d7_family_odd`, `d7_family_even`, and `d7_family`: for every prime power `q >= 5` (`IsPrimePow q`)
  `∃ G : SimpleGraph (Fin (6 * ((q^6 - 1)/(q - 1)) + 2*(q^2+1))), IsBipartiteDegDiam G (q+2) 7`
  (via the Galois field of order `q`; `Nq_eq` identifies `(q^6-1)/(q-1)` with `(q+1)(1+q^2+q^4)`).
- `Axioms.out.txt`: `d7_of_sets`, `d7_odd`, `d7_even`, `d7_family_odd`, `d7_family_even`, `d7_family` depend only on
  propext, Classical.choice, Quot.sound. No sorry, admit or native_decide under `LeanMaxx/`.

## Status: complete

The note's Corollary 9.1 is formalised for every prime power `q >= 5`. Nothing remains.
Environment note: the cloud image had no Lean; install by unpacking the lean4 release tarball into
`~/.elan/toolchains/leanprover--lean4---v4.34.1`, then `lake update; lake exe cache get` in `lean/`.
