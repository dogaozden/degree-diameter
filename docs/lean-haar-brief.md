Lean 4 + Mathlib. Work on your own for up to 5 hours; do not ask for approval. Lean checks every proof; iterate until builds pass. Push after every milestone.

Setup: `git fetch origin && git checkout -b lean-haar origin/claude/lean-d5-record-theorems-th6ybb && git merge origin/research-diam4` (take research-diam4's version for conflicts outside lean/). Install elan (`curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none`, `source ~/.elan/env`), `lake exe cache get` in lean/. `git push -u origin HEAD`.

Read research/d5/REPORT.md first (the Haar lemma and the records).

## Task 1: the Haar lemma (general, in lean/BipartiteDD/Haar/)
For a finite group G (with DecidableEq) and a Finset S ⊆ G, the Haar graph has vertex set G ⊕ G, with (g, A) adjacent to (s·g, B) for s ∈ S (define it as a SimpleGraph on `G ⊕ G`; adjacency symmetric; no edges within a side).
Prove:
- `haar_colorable`: Colorable 2.
- `haar_degree`: every vertex has degree |S| (or ≤ |S|; ≤ is enough).
- `haar_ediam_le_five`: if every g ∈ G is a product a⁻¹·b·c⁻¹·d with a, b, c, d ∈ S, and every g ∈ G is a product a·b⁻¹·c·d⁻¹ with a, b, c, d ∈ S, and S is nonempty, then ediam ≤ 5. (Proof idea: right multiplication by any h is a graph automorphism, so it suffices to bound distances from (1, A) and (1, B); the A-vertices within distance 4 of (1, A) are (S⁻¹S)², the B-vertices within 4 of (1, B) are (SS⁻¹)², and odd distances go one step further. Check which order of the products matches your adjacency convention; adjust the hypothesis, not the conclusion.)
- `haar_isBipartiteDegDiam`: combine into `IsBipartiteDegDiam (haarGraph G S) S.card 5`, and transport to `Fin (2 * Fintype.card G)` like the other files do.

## Task 2: the (9,5) record 2620 via the Haar lemma
The group is Z_131 ⋊_53 Z_10: pairs (x, y) with x ∈ ZMod 131, y ∈ ZMod 10, and the product convention used in research/d5/build_haar.py (read `mul` there, and check by computation that 53 has multiplicative order dividing 10 mod 131). S is in research/d5/sols/h2_d9_N1310_m131_k10_l53.txt (first line "Δ m k λ", then Δ lines "x y"). Define the group as a concrete Lean structure (a `Group` instance on ZMod 131 × ZMod 10 with that product; prove the group axioms, by `decide` if needed). Prove the two covering hypotheses by a kernel computation (`decide` or `Finset` computation; no native_decide), and conclude
`nb_9_5_v3 : ∃ G : SimpleGraph (Fin 2620), BipartiteDD.IsBipartiteDegDiam G 9 5`.
If the kernel computation is slow, split the covering check into chunks (each a separate theorem).
Optional, only if time remains: redo nb_8_5 (Z_144 ⋊_25 Z_6, graph records/bipartite_dd/d8D5/1728-*.json "construction" field) the same way, as nb_8_5_haar.

## Rules
No `sorry`, `admit`, new `axiom`, `native_decide`, or checking-weakening options. Do not change IsBipartiteDegDiam, check_sound or existing theorems; do not edit GQ4/, GQST/, ASq/, SingerC/, Plus2/. Add new theorems to Axioms.lean, regenerate Axioms.out.txt, commit `milestone: ...`, push.

## Final reply
What builds, the exact statements proved, `#print axioms` lines, build times, last commit hash.
