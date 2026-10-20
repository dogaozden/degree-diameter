# Lean brief: Proposition C in full, and Corollary C1 (Sonnet; takes over the Haiku work on lean-c1)

Read first: research/NOTE.md Section 5 (Prop C, its proof, Cor C1), docs/lean-c1-brief.md (the plan: build everything on
W(3,q) directly, so no Klein correspondence is needed), lean/BipartiteDD/SingerC/*.lean on master (the Singer setting,
the form `S.B`, `propC_subspace`), lean/BipartiteDD/GQST/*.lean (the copy theorem `GQST.gqst`, and `standin_gqst`).

Starting point: branch `origin/lean-c1` has ~790 lines of work in progress by a Haiku session (SingerC/W3Basic,
W3Lines, W3Ovoid, W3Spread, W3Main), not yet on the import chain, at least one `sorry` (W3Basic), and not known to build.
That Haiku session may push to lean-c1 until about 8:15 PM; do not push to lean-c1. Work on your own branch
`lean-propC`, started from origin/lean-c1. Reuse what is correct, rewrite what is not.

## Targets (in this order; push after each)
1. `W3.isGQst : GQst (ℙ S.F K) (W3Line S) S.q S.q` — W(3,q) on the Singer setting is a GQ of order (q,q).
2. `propC : ∀ a ≤ q, ∀ l : W3Line S, card {x : ℙ S.F K | x ≤ l ∧ x ∈ O_a} = 2`, where O_a is the set of points in Singer
   classes a or q−a. This is Proposition C as stated in the NOTE (C_a ∪ C_{q−a} is a 2-ovoid of W(3,q)), from
   `propC_subspace` (2(q−1) nonzero vectors ⇒ 2 points).
3. The regular spread {x·L}: every point is on exactly one spread line, all spread lines are totally isotropic.
4. `corC1 (S) {j} (hj : Even j) (hj2 : 2 ≤ j) : ∃ H : SimpleGraph (Fin (2 * (S.q ^ 2 + 1) * (S.q + 1 + j))),
   IsBipartiteDegDiam H (S.q + 1 + j) 4` through `GQST.gqst` with w = (j/2)·1_O, m = j·1_spread, a = b = j.
5. Add `#print axioms` for W3.isGQst, propC, corC1 to lean/Axioms.lean; regenerate lean/Axioms.out.txt; put the new
   files on the import chain.

## Rules
- Before each step run `scripts/stop_check.sh`; if it prints STOP, commit, push, end.
- Long commands through `scripts/guarded.sh HOURS ...`; total limit 5 hours; build one heavy module at a time.
- No `sorry`, `admit`, `axiom`, `native_decide` in finished files; only propext, Classical.choice, Quot.sound.
- Report: targets done, exact statements, build result, axioms lines; if something is left, the exact lemma and why.
