You are formalizing a theorem in Lean 4 with Mathlib. Work on your own for up to 6 hours; do not ask for approval. Lean checks every proof, so keep iterating; prove one lemma at a time and build after each.

## The theorem (informal; read research/gq4x/REPORT.md sections 1–2 first)
For a finite field F of odd order q: the Ahrens–Szekeres quadrangle AS(q) is a generalized quadrangle of order (q−1, q+1), and two elliptic quadrics in it form a weighted 2-ovoid. With the copy theorem already in Lean (`GQST.gqst` on branch lean-gqst) this gives: there is a bipartite graph on 2q²(q+2) vertices with maximum degree q+2 and diameter 4.

Concretely (REPORT.md §1–2):
- Points: F × F² (q³ of them), written (a, w), w = (b, c). Group law (a,w)(a',w') = (a + a' + det(w,w'), w + w'), det((b,c),(b',c')) = bc' − cb'.
- Lines, two kinds: for each direction d ∈ F² \ {0} up to F*-scaling (q+1 classes) and each point (a0,w0), the coset {(a0 + λ·det(w0,d), w0 + λd) : λ ∈ F}; and the fibres {(μ, w) : μ ∈ F} for each w. Each line has q points, each point is on q+2 lines, there are (q+2)q² lines. (Represent lines as Finsets of points, or by canonical parameters; your choice.)
- ε a non-square in F, N(b,c) = b² − εc². For c ≠ 0, Q_c = {(c·N(w), w) : w ∈ F²}. Choose c1, c2 with c1·c2 = 1/(4ε). The weight w(p) = [p ∈ Q_c1] + [p ∈ Q_c2] satisfies Σ_{p ∈ L} w(p) = 2 for every line L (proof: REPORT.md §2 steps 1–7, a discriminant identity B² − 4N(w0)N(d) = 4εD² and quadratic-character counting).

## Statements to prove (in lean/BipartiteDD/ASq/, imported from lean/BipartiteDD.lean)
1. `ASq.isGQst`: for `F` a finite field with `ringChar F ≠ 2`, the AS incidence structure is a `GQst P L (q-1) (q+1)` with q = Fintype.card F (use `GQst` from lean-gqst's `BipartiteDD/GQST/Defs.lean`).
2. `ASq.weighted_two_ovoid`: Σ_{p ∈ L} w(p) = 2 for every line L.
3. `ASq.bound`: `∃ H : SimpleGraph (Fin (2 * q^2 * (q + 2))), IsBipartiteDegDiam H (q + 2) 4` for every finite field of odd order (from 1, 2, `GQST.gqst` with a = 2, m = 0, b = 0, and a cardinality computation).
If (1) in full generality is too hard, prove it first for `ZMod p`, p an odd prime (note in the final reply), then generalize if time allows. Partial progress counts: push each proved lemma.

## Setup and rules
`git fetch origin && git checkout -b lean-asq origin/lean-gqst && git merge origin/research-diam4` (take research-diam4's version for conflicts outside lean/). Install elan (`curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none`, `source ~/.elan/env`); `lake exe cache get` in lean/. Push with `git push -u origin HEAD` and after every milestone. Do not edit GQ4/, GQST/, Plus2/, Records.lean, Fast.lean, Staged.lean, Basic.lean or graph data files. No `sorry`, `admit`, new `axiom`, `native_decide`, or checking-weakening options. At the end add the new theorems to `lean/Axioms.lean`, regenerate `lean/Axioms.out.txt`, commit with a message starting `milestone:`, push.

## Final reply
What builds, the exact statements proved (copy them), `#print axioms` lines, what is still open, last commit hash.
