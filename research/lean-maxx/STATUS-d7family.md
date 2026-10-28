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

## To do

- odd q: elliptic quadric points `(1, a, 0, b, b^2 - λa^2, λa, 0)` and `e_4` (λ a non-square), `S` inside the
  Hermitian spread `SLine c` (HexagonD/Spread.lean).
- even q: the same with HexagonEven/Spread.lean and a char-2 elliptic quadric section.
