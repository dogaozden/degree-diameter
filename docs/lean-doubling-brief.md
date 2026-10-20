# Lean brief: Delorme's levelled doubling and the hat lemma (Problem 4 theory)

Read research/p4/hats/REPORT.md Section 1 (Theorem 1 with proof, Lemma 2 with proof) and the existing copy-lemma Lean
files on master (lean/BipartiteDD/GQST/Blowup.lean, Diam.lean, Main.lean, Standin*.lean) for style and API.

Targets (new folder lean/BipartiteDD/Doubling/; push after each):
1. Single-level doubling of a graph G along A ⊆ V (vertex type V ⊕ A; edges as in the report). Prove: bipartite if G is;
   max degree ≤ Δ+1 under condition (b); ediam ≤ D under (c) when G has ediam ≤ D (D ≥ 2).
2. Levels A0 ⊇ A1 ⊇ … with m-ary strings (Theorem 1 in full), degree ≤ Δ+m−1 under (a),(b), diameter ≤ D under (c),
   and the order formula. If the general version is too heavy, do m = 2 with finitely many levels first.
3. Lemma 2 for the incidence graph of a generalized n-gon (define it as a bipartite graph of girth 2n, diameter n, and
   every vertex of degree ≥ 2): condition (c) holds iff each component of G[A0] is a tree of diameter ≤ n−2. At least
   the "if" direction (that is the one the constructions use).
Rules: `scripts/stop_check.sh` before each step; builds through `scripts/guarded.sh HOURS ...`; total limit 5 hours.
No `sorry`, `admit`, `axiom`, `native_decide` in finished files; only the three standard axioms. Branch `lean-doubling`.
Report: theorem statements, build result, axioms lines, what is left.
