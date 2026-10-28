# STATUS: omega2 (Gómez ΩH_q, Theorem 2 of research/squads/cells/d12D8_table.md §2)

**In progress.** Files under lean/BipartiteDD/LeanMaxx/Omega2/.

- `Sphere.lean` (builds, no sorry): sphere sizes in a generalized hexagon of order (q,q):
  `card_sph_zero`, `card_sph_one`, `card_sph_five` (= (q+1) q^4), `card_sph_succ`, `q_pow_five_le_card_sph_six`.
  Girth ⇒ unique predecessor (`pred_unique`) via a cycle built from `Walk.bypass`.
