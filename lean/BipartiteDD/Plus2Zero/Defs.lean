import Mathlib.Combinatorics.Configuration
import BipartiteDD.Basic

/-! Zero-change `+2`: the four hats without changing the plane (`research/plus3/plus3.tex`,
Proposition `prop:zero`; `research/plus3/construction0.py`). Every incidence of the projective
plane is kept. The rotation `1 ↦ 2 ↦ 3 ↦ 1` lives on the copies: `H i` also lies on `AX (s i)`
and `K i` also contains `X (s⁻¹ i)`. -/

namespace BipartiteDD.Plus2Zero
open Configuration

/-- The four hats: `a` (copying `X a`) and `one`, `two`, `three` (copying `X one`, `X two`,
`X three`). -/
inductive Hat | a | one | two | three
  deriving DecidableEq

instance : Fintype Hat := ⟨{.a, .one, .two, .three}, fun x => by cases x <;> decide⟩

/-- The new points: `Q` (copy of `A`) and the hat points `H h` (copies of `X h`). -/
inductive NewPt | Q | H (h : Hat)
  deriving DecidableEq

/-- `NewPt` is `Option Hat` with `none ↦ Q` and `some h ↦ H h`. -/
instance : Fintype NewPt :=
  Fintype.ofEquiv (Option Hat)
    { toFun := fun o => match o with | none => .Q | some h => .H h
      invFun := fun v => match v with | .Q => none | .H h => some h
      left_inv := fun o => by cases o <;> rfl
      right_inv := fun v => by cases v <;> rfl }

/-- The new lines: `M` (copy of `ℓ`) and the hat lines `K h` (copies of `AX h`). -/
inductive NewLn | M | K (h : Hat)
  deriving DecidableEq

/-- `NewLn` is `Option Hat` with `none ↦ M` and `some h ↦ K h`. -/
instance : Fintype NewLn :=
  Fintype.ofEquiv (Option Hat)
    { toFun := fun o => match o with | none => .M | some h => .K h
      invFun := fun v => match v with | .M => none | .K h => some h
      left_inv := fun o => by cases o <;> rfl
      right_inv := fun v => by cases v <;> rfl }

/-- The 3-cycle `1 ↦ 2 ↦ 3 ↦ 1` on the hats `one`, `two`, `three`; `a` is fixed. -/
def rot : Hat → Hat
  | .a => .a
  | .one => .two
  | .two => .three
  | .three => .one

/-- The inverse 3-cycle `s⁻¹`. -/
def rotInv : Hat → Hat
  | .a => .a
  | .one => .three
  | .two => .one
  | .three => .two

/-- The choices: a line `ℓ`, a point `A` off it, and four distinct points `X h` on it. -/
structure Frame (P L : Type*) [Membership P L] where
  ell : L
  A : P
  X : Hat → P
  A_not_mem : A ∉ ell
  X_mem : ∀ h, X h ∈ ell
  X_inj : Function.Injective X

variable {P L : Type*} [Membership P L] [ProjectivePlane P L]

theorem Frame.A_ne_X (F : Frame P L) (h : Hat) : F.A ≠ F.X h :=
  fun e => F.A_not_mem (e ▸ F.X_mem h)

/-- The line through `A` and `X h`. -/
noncomputable def Frame.AX (F : Frame P L) (h : Hat) : L := HasLines.mkLine (F.A_ne_X h)

/-- Incidence of the new structure. Plane incidences are unchanged (first arm). The copies
carry the rule of `prop:zero`: `Q` sees the lines through `A` except `AX one, AX two, AX three`;
`H h` sees the lines through `X h` except `ℓ` and `AX h` (for `h ≠ a`), plus `AX (rot h)`;
`K h` sees the points of `AX h` except `A` and `X h` (for `h ≠ a`), plus `X (rotInv h)`. -/
def Frame.inc (F : Frame P L) : P ⊕ NewPt → L ⊕ NewLn → Prop
  | .inl p, .inl l => p ∈ l
  | .inl p, .inr .M => p ∈ F.ell ∧ p ≠ F.X .one ∧ p ≠ F.X .two ∧ p ≠ F.X .three
  | .inl p, .inr (.K .a) => p ∈ F.AX .a ∧ p ≠ F.X .a
  | .inl p, .inr (.K .one) => (p ∈ F.AX .one ∧ p ≠ F.A ∧ p ≠ F.X .one) ∨ p = F.X .three
  | .inl p, .inr (.K .two) => (p ∈ F.AX .two ∧ p ≠ F.A ∧ p ≠ F.X .two) ∨ p = F.X .one
  | .inl p, .inr (.K .three) => (p ∈ F.AX .three ∧ p ≠ F.A ∧ p ≠ F.X .three) ∨ p = F.X .two
  | .inr .Q, .inl l => F.A ∈ l ∧ l ≠ F.AX .one ∧ l ≠ F.AX .two ∧ l ≠ F.AX .three
  | .inr .Q, .inr .M => False
  | .inr .Q, .inr (.K _) => True
  | .inr (.H .a), .inl l => F.X .a ∈ l ∧ l ≠ F.AX .a
  | .inr (.H .one), .inl l => (F.X .one ∈ l ∧ l ≠ F.ell ∧ l ≠ F.AX .one) ∨ l = F.AX .two
  | .inr (.H .two), .inl l => (F.X .two ∈ l ∧ l ≠ F.ell ∧ l ≠ F.AX .two) ∨ l = F.AX .three
  | .inr (.H .three), .inl l => (F.X .three ∈ l ∧ l ≠ F.ell ∧ l ≠ F.AX .three) ∨ l = F.AX .one
  | .inr (.H _), .inr .M => True
  | .inr (.H h), .inr (.K k) => h = k

/-- The incidence graph: points on the left, lines on the right. -/
def Frame.graph (F : Frame P L) : SimpleGraph ((P ⊕ NewPt) ⊕ (L ⊕ NewLn)) where
  Adj u v := match u, v with
    | .inl p, .inr l => F.inc p l
    | .inr l, .inl p => F.inc p l
    | _, _ => False
  symm := ⟨fun u v h => by
    rcases u with p | l <;> rcases v with q | m <;> first | exact h | exact (show False from h).elim⟩
  loopless := ⟨fun u h => by
    rcases u with p | l <;> exact h⟩

end BipartiteDD.Plus2Zero
