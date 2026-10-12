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
  symm := by
    intro u v h
    rcases u with p | l <;> rcases v with q | m <;> first | exact h | exact h.elim
  loopless := by
    intro u h
    rcases u with p | l <;> exact h
