# Lean brief: Theorem B in full (line copies with stand-ins)

Goal: extend `BipartiteDD.GQST` (lean/BipartiteDD/GQST/*.lean, on master) from "all stand-ins original" to Theorem B
of research/NOTE.md Section 2 (read it: construction, statement, proof with the three distance cases).

## Autopilot rules (always)
- Before each step, run `scripts/stop_check.sh`. If it prints STOP: commit what you have, push, and end.
- Long commands go through `scripts/guarded.sh HOURS ...`. Total time limit: 4 hours. Commit and push progress
  (with `sorry`-free files only, or clearly marked WIP files not imported by the main target) every hour.
- Build one heavy module at a time.

## What to formalise
Data: a GQ `G : GQst P L s t` with `1 ≤ s`, `1 ≤ t`; point weights `w : P → ℕ`; line-copy counts `m : L → ℕ`;
a stand-in choice `σ : (c : Σ l, Fin (m l)) → (p : P) → p ∈ c.1 → Fin (w p + 1)` (0 = the original point,
i+1 = copy i of p).
Graph `standin P L w m σ` on `(P ⊕ Σ p, Fin (w p)) ⊕ (L ⊕ Σ l, Fin (m l))`:
- original line l ~ original point p and every copy of p, for p ∈ l (as in `blowup`);
- line copy c = ⟨l, i⟩ ~ the stand-in σ c p of each p ∈ l, and nothing else.
Theorems:
1. `standin_colorable`: 2-colourable.
2. `standin_ediam`: ediam ≤ 4. Follow the NOTE's proof: the part without line copies is the existing `blowup` with
   `m = 0`; then the three cases point/line copy, original line/line copy, line copy/line copy.
3. `standin_degree`: max degree ≤ max (s + 1 + a) (t + 1 + b) when every line has total point weight ≤ a and each
   stand-in (p, k) serves at most b line copies.
4. `standin_isBipartiteDegDiam` and a `Fin n` version with n = |P| + |L| + Σ w + Σ m, like `GQST.gqst`.
5. Check: with σ ≡ 0 the graph equals `blowup` (a short lemma), so nothing old is contradicted.

## Steps
1. Branch `lean-thmB` from origin/master; `lake exe cache get`.
2. New files under lean/BipartiteDD/GQST/ (e.g. Standin.lean, StandinDiam.lean); add `#print axioms` lines for the main
   theorems to lean/Axioms.lean and regenerate lean/Axioms.out.txt.
3. No `sorry`, `admit`, `axiom` or `native_decide` in finished files; axioms only propext, Classical.choice, Quot.sound.
4. Commit and push to `lean-thmB`. Short report: files, theorem statements, build result, axioms lines.
