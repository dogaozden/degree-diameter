You are formalizing a theorem in Lean 4 with Mathlib. Work on your own for up to 6 hours; do not ask for approval. Lean checks every proof, so keep iterating on compiler errors until the build passes. Prove one lemma at a time, building after each.

## The theorem (informal)
The +2 construction: take any finite projective plane of order q, a line ℓ, a point A not on ℓ, and five distinct points P0, X0, X1, Xa, Xc on ℓ. Build an incidence structure with five new points (Q, H0, H1, Ha, Hc) and five new lines (M, K0, K1, Ka, Kc). Its incidence graph is bipartite, has maximum degree q + 2 and diameter at most 3, and has 2(q² + q + 6) vertices. The full informal proof is in `research/plus2/REPORT.md`, sections 3 and 4. Read it first; your Lean proof follows it.

## Setup
1. `git fetch origin && git checkout -b lean-plus2 2f0b9d430` (the last built commit of the Lean project), then `git merge origin/master` (take master's version of anything outside `lean/`). Push with `git push -u origin HEAD`.
2. Install elan: `curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none`, then `source ~/.elan/env`. In `lean/`, run `lake exe cache get`.
3. Put all new code in `lean/BipartiteDD/Plus2/` (several files are fine). Build with `lake build BipartiteDD.Plus2.Main` (or similar). Do not edit `BipartiteDD/Basic.lean`, `Records.lean`, `Fast.lean` or the graph data files: another session is changing them on a different branch.
4. Mathlib API you will use: `Mathlib/Combinatorics/Configuration.lean`. `Configuration.ProjectivePlane P L`, `HasLines.mkLine`, `HasLines.mkLine_ax`, `HasPoints.mkPoint`, `HasPoints.mkPoint_ax`, `Nondegenerate.eq_or_eq` (two points on two lines: the points are equal or the lines are), `ProjectivePlane.order`, `ProjectivePlane.lineCount_eq` (`lineCount L p = order P L + 1`), `ProjectivePlane.pointCount_eq`, `ProjectivePlane.card_points`, `ProjectivePlane.card_lines`. `lineCount L p = Nat.card {l : L // p ∈ l}`. Find exact names by grepping `.lake/packages/mathlib/Mathlib/`; use `exact?`/`apply?`.

## Definitions (use these; fix only syntax errors, and report any change)
```lean
import Mathlib.Combinatorics.Configuration
import BipartiteDD.Basic

namespace BipartiteDD.Plus2
open Configuration

/-- The four hat rows 0, 1, a, c. -/
inductive Row | r0 | r1 | ra | rc
  deriving DecidableEq, Fintype

/-- The five new points: Q and the hat points H s. -/
inductive NewPt | Q | H (s : Row)
  deriving DecidableEq, Fintype

/-- The five new lines: M and the hat lines K s. -/
inductive NewLn | M | K (s : Row)
  deriving DecidableEq, Fintype

/-- The 3-cycle used twice: X t goes on line AX s, and hat point H t goes on hat line K s,
exactly for (t, s) = (1, 0), (c, 1), (0, c). -/
def cyc : Row → Row → Bool
  | .r1, .r0 => true
  | .rc, .r1 => true
  | .r0, .rc => true
  | _, _ => false

/-- The choices: a line ℓ, a point A off ℓ, and five distinct points of ℓ (P0 and the feet X s). -/
structure Frame (P L : Type*) [Membership P L] where
  ell : L
  A : P
  P0 : P
  X : Row → P
  A_not_mem : A ∉ ell
  P0_mem : P0 ∈ ell
  X_mem : ∀ s, X s ∈ ell
  X_inj : Function.Injective X
  X_ne_P0 : ∀ s, X s ≠ P0

variable {P L : Type*} [Membership P L] [ProjectivePlane P L]

theorem Frame.A_ne_X (F : Frame P L) (s : Row) : F.A ≠ F.X s :=
  fun h => F.A_not_mem (h ▸ F.X_mem s)

/-- The line through A and X s. -/
noncomputable def Frame.AX (F : Frame P L) (s : Row) : L := HasLines.mkLine (F.A_ne_X s)

/-- Incidence of the new structure: rules 1–6 of REPORT.md section 3. -/
def Frame.inc (F : Frame P L) : P ⊕ NewPt → L ⊕ NewLn → Prop
  | .inl p, .inl l => (p ∈ l ∧ ¬ ∃ s, p = F.X s ∧ l = F.AX s) ∨ ∃ t s, cyc t s ∧ p = F.X t ∧ l = F.AX s
  | .inl p, .inr .M => p ∈ F.ell ∧ p ≠ F.X .r0 ∧ p ≠ F.X .r1 ∧ p ≠ F.X .rc
  | .inl p, .inr (.K s) => (p ∈ F.AX s ∧ p ≠ F.A) ∨ (s = .ra ∧ p = F.A)
  | .inr .Q, .inl l => F.A ∈ l ∧ l ≠ F.AX .r0 ∧ l ≠ F.AX .r1 ∧ l ≠ F.AX .rc
  | .inr .Q, .inr .M => False
  | .inr .Q, .inr (.K _) => True
  | .inr (.H s), .inl l => (F.X s ∈ l ∧ l ≠ F.ell) ∨ (s = .ra ∧ l = F.ell)
  | .inr (.H _), .inr .M => True
  | .inr (.H s), .inr (.K t) => cyc s t

/-- The incidence graph: points on the left, lines on the right. -/
def Frame.graph (F : Frame P L) : SimpleGraph ((P ⊕ NewPt) ⊕ (L ⊕ NewLn)) where
  Adj u v := match u, v with
    | .inl p, .inr l => F.inc p l
    | .inr l, .inl p => F.inc p l
    | _, _ => False
  symm := by sorry   -- fill in
  loopless := by sorry  -- fill in
```
How the rules map: the plane-point/plane-line case is rule 1 (remove X s ∈ AX s, add the rotation); M is rule 4; K s is rule 3 plus "A on Ka" (rule 6); Q's plane lines are "AX for X ∈ ℓ*", i.e. lines through A other than AX0, AX1, AXc (rule 5); H s is rule 2 plus "Ha on ℓ" (rule 6); H s ∈ K t is the cycle of rule 6.

## Lemmas to prove, in order (milestone after each group)
**Group A — basic facts.** Commit with `milestone: plus2 A`.
- `Frame.graph` `symm` and `loopless`.
- `Frame.X_mem_AX (s) : F.X s ∈ F.AX s` and `Frame.A_mem_AX (s) : F.A ∈ F.AX s` (from `mkLine_ax`).
- `Frame.AX_inj : Function.Injective F.AX` (two such lines share A; if equal they would share both X s and X t, which lie on ℓ, contradiction with `eq_or_eq` and `A_not_mem`).
- `Frame.AX_ne_ell (s) : F.AX s ≠ F.ell`.
- `Frame.mem_AX_iff (s) {p} (hp : p ∈ F.ell) : p ∈ F.AX s ↔ p = F.X s` (AX s meets ℓ only at X s).
- `Frame.eq_A_of_mem_AX_AX {s t} (h : s ≠ t) {p} (h1 : p ∈ F.AX s) (h2 : p ∈ F.AX t) : p = F.A`.
- A general graph lemma, independent of planes: for a graph built like `Frame.graph` from any `inc : α → β → Prop`, if (i) every two left vertices have a common right neighbour and (ii) every two right vertices have a common left neighbour, then `ediam ≤ 3`. Proof: point–point and line–line are distance ≤ 2; for a point p and a line l, take a point p′ on l (from (ii) applied to l, l), then a line l′ through p and p′ (from (i)): the walk p–l′–p′–l has length 3. Use `SimpleGraph.ediam_le_iff` / `edist_le` with explicit walks.
- `Frame.colorable : F.graph.Colorable 2` (colour by `Sum.isLeft`).

**Group B — any two points share a line.** `Frame.collinear (p q : P ⊕ NewPt) : ∃ l, F.inc p l ∧ F.inc q l`. Follow REPORT.md section 4, Step 2, cases (a)–(d). For two plane points u ≠ v use `L₀ := mkLine` through them; if u = v use any line through u with the needed property. Split into sub-lemmas (one per case) and prove each separately. Commit `milestone: plus2 B`.

**Group C — any two lines share a point.** `Frame.concurrent (l m : L ⊕ NewLn) : ∃ p, F.inc p l ∧ F.inc p m`. The report proves this by duality; in Lean, prove it directly by cases instead. The dual dictionary tells you the witness in each case: swap points and lines with Q ↔ M, A ↔ ℓ, H0 ↔ K0, H1 ↔ Kc, Ha ↔ Ka, Hc ↔ K1, X0 ↔ AX0, X1 ↔ AXc, Xa ↔ AXa, Xc ↔ AX1, "point on line" ↔ "line through point", "line through two points" ↔ "intersection point of two lines" (`mkPoint`). Take each case of Step 2, translate it, and prove the translated statement. Commit `milestone: plus2 C`.

**Group D — degrees.** With `[Finite P] [Finite L]`, let q := `ProjectivePlane.order P L`.
- `Frame.point_degree (p) : Nat.card {l : L ⊕ NewLn // F.inc p l} ≤ q + 2`
- `Frame.line_degree (l) : Nat.card {p : P ⊕ NewPt // F.inc p l} ≤ q + 2`
Follow REPORT.md Step 1, one case per kind of vertex. Recipe: show the incident set is contained in `Sum.inl '' S ∪ Sum.inr '' T`, where S is "the lines through p" minus or plus at most a known set, and T is a small explicit set of new lines; then bound cardinalities using `lineCount_eq` / `pointCount_eq`. A helper like `Nat.card {x : α ⊕ β // r x} ≤ Nat.card {a // r (.inl a)} + Nat.card {b // r (.inr b)}` will be used everywhere; prove it once. Then turn these into `(F.graph.neighborSet v).ncard ≤ q + 2`. Commit `milestone: plus2 D`.

**Group E — the main theorem.** Commit `milestone: plus2 E` with these, statements exactly as written:
```lean
theorem Frame.isBipartiteDegDiam [Fintype P] [Fintype L] (F : Frame P L) :
    IsBipartiteDegDiam F.graph (ProjectivePlane.order P L + 2) 3

theorem plus2 {P L : Type*} [Membership P L] [ProjectivePlane P L] [Fintype P] [Fintype L]
    (F : Frame P L) :
    ∃ G : SimpleGraph (Fin (2 * (ProjectivePlane.order P L ^ 2 + ProjectivePlane.order P L + 6))),
      IsBipartiteDegDiam G (ProjectivePlane.order P L + 2) 3
```
For `plus2`: the vertex type has card `2 * (q^2 + q + 6)` (use `card_points`, `card_lines`, and `Fintype.card` of the inductives = 5); transport the graph along `Fintype.equivFin`. Prove a lemma that `IsBipartiteDegDiam` is preserved by a graph isomorphism (`SimpleGraph.Iso`).

**Group F (stretch).** `Frame.exists (h : 4 ≤ ProjectivePlane.order P L) [Fintype P] [Fintype L] : Nonempty (Frame P L)` (pick a line, a point off it, five distinct points on the line, possible since it has q + 1 ≥ 5 points), and then
```lean
theorem plus2_of_order {P L : Type*} [Membership P L] [ProjectivePlane P L] [Fintype P] [Fintype L]
    (h : 4 ≤ ProjectivePlane.order P L) :
    ∃ G : SimpleGraph (Fin (2 * (ProjectivePlane.order P L ^ 2 + ProjectivePlane.order P L + 6))),
      IsBipartiteDegDiam G (ProjectivePlane.order P L + 2) 3
```
Commit `milestone: plus2 F`.

## Rules
- No `sorry`, no `admit`, no new `axiom`, no `native_decide`, no options that weaken checking, in the final state. (`sorry` is fine while working, but every milestone commit must build without it for the lemmas it claims.)
- Do not change the definitions or the Group E statements except to fix syntax; report any change word for word.
- Add `lean/BipartiteDD/Plus2/Axioms.lean` running `#print axioms` on `plus2` (and `plus2_of_order` if done), and commit its output as `Axioms.out.txt`.
- Commit and push after every milestone.

## Final reply
Which groups are done, the `#print axioms` output, any change to definitions or statements, and the commit hash of your last push.
