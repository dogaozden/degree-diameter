/-! # The packed batch check, without Mathlib

The definitions of `HaarSwar.lean` that a batch module evaluates (parameters, letters, states, one step, all
steps, `batchOK`), of `HaarSL.lean` (`invLet`, `kindB`, `aB`, `cB`) and of `Blocks.lean` (`blk`), copied word for
word into new namespaces so that the batch modules of a cell import no Mathlib (Lean starts in about 0.4 s
instead of 2.4 s). `HaarSwar2.lean` and `HaarSL2.lean` carry the proofs of `HaarSwar.lean` and `HaarSL.lean` over
these definitions. -/

namespace BipartiteDD.LeanAll.HaarSwar2

/-! ## Parameters -/

/-- Field width `w`, slots `N`, prime `p`, cyclic order `n`, Barrett shift `s` and multiplier `m`,
number of generators `Δ`, letters `L`. -/
structure Prm where
  w : Nat
  N : Nat
  p : Nat
  n : Nat
  s : Nat
  m : Nat
  Δ : Nat
  L : Nat

/-- The size conditions the soundness proof uses (all decidable, checked per cell). -/
def Prm.valid (P : Prm) : Prop :=
  8 ≤ P.w ∧ 4 * P.L + 4 ≤ P.w ∧ P.Δ ≤ 16 ∧ 2 ≤ P.p ∧ 1 ≤ P.n ∧ P.s ≤ P.w ∧
  2 * P.p * P.p ≤ 2 ^ (P.w - 1) ∧ 2 * P.n ≤ 2 ^ (P.w - 1) ∧
  2 * P.p * P.p * P.m < 2 ^ P.w ∧ P.m * P.p ≤ 2 ^ P.s

instance (P : Prm) : Decidable P.valid := by unfold Prm.valid; infer_instance

/-- A letter: matrix entries `e f g h` (row-major) and the `Z_n` shift `zw`. -/
structure Let where
  e : Nat
  f : Nat
  g : Nat
  h : Nat
  zw : Nat

/-- A packed state: one number per entry, plus the `Z_n` part. -/
structure St where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  z : Nat

/-! ## The packed computation -/

section Comp

variable (P : Prm) (ONES : Nat) (lt : Nat → Nat → Let)

/-- `[digit ≥ u]` per field, from the digit fields `Dt` (values `< 16`). -/
def thr (Dt u : Nat) : Nat := ((Dt + (16 - u) * ONES) >>> 4) &&& ONES

/-- `[digit = u]` per field. -/
def eqm (Dt u : Nat) : Nat := thr ONES Dt u - thr ONES Dt (u + 1)

/-- `Σ_{u < k} sel(V u)`: the value of the slot's own letter, per field. -/
def selSum (Dt : Nat) (V : Nat → Nat) (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun u acc => acc + (V u &&& (eqm ONES Dt u * (2 ^ P.w - 1)))) k

/-- Reduction mod `p` of a packed number with fields `< 2 p²`. -/
def red (q V : Nat) : Nat :=
  let Q := ((V * P.m) >>> P.s) &&& ((2 ^ (P.w - P.s) - 1) * ONES)
  let R := V - q * Q
  let T := ((R + (2 ^ (P.w - 1) - q) * ONES) >>> (P.w - 1)) &&& ONES
  R - q * T

/-- Reduction mod `n` of a packed number with fields `< 2 n`. -/
def redZ (V : Nat) : Nat :=
  let T := ((V + (2 ^ (P.w - 1) - P.n) * ONES) >>> (P.w - 1)) &&& ONES
  V - P.n * T

/-- Every field is below `q`. -/
def below (q V : Nat) : Bool :=
  Nat.beq ((V + (2 ^ (P.w - 1) - q) * ONES) &&& (2 ^ (P.w - 1) * ONES)) 0

/-- One step `t`: multiply every slot by its letter. -/
def stepP (Dig t : Nat) (X : St) : St × Bool :=
  let Dt := (Dig >>> (4 * t)) &&& (15 * ONES)
  let A := red P ONES P.p (selSum P ONES Dt (fun u => X.a * (lt t u).e + X.b * (lt t u).g) P.Δ)
  let Bq := red P ONES P.p (selSum P ONES Dt (fun u => X.a * (lt t u).f + X.b * (lt t u).h) P.Δ)
  let C := red P ONES P.p (selSum P ONES Dt (fun u => X.c * (lt t u).e + X.d * (lt t u).g) P.Δ)
  let D := red P ONES P.p (selSum P ONES Dt (fun u => X.c * (lt t u).f + X.d * (lt t u).h) P.Δ)
  let Z := redZ P ONES (X.z + selSum P ONES Dt (fun u => (lt t u).zw * ONES) P.Δ)
  (⟨A, Bq, C, D, Z⟩, Nat.beq (thr ONES Dt P.Δ) 0 && below P ONES P.p A && below P ONES P.p Bq &&
    below P ONES P.p C && below P ONES P.p D && below P ONES P.n Z)

/-- All `L` steps from the identity. -/
def runP (Dig : Nat) : St × Bool :=
  Nat.rec (motive := fun _ => St × Bool) (⟨ONES, 0, 0, ONES, 0⟩, true)
    (fun t acc => let r := stepP P ONES lt Dig t acc.1; (r.1, acc.2 && r.2)) P.L

end Comp

/-- The batch check: the certificate fits, every step passes, and the final entries are the targets
(`a`, `c`, `z` and, by `kind`, `b` or `d`). -/
def batchOK (P : Prm) (ONES : Nat) (lt : Nat → Nat → Let) (Dig : Nat) (kind : Bool) (TA TB TC TD TZ : Nat) : Bool :=
  Nat.blt Dig (2 ^ (P.w * P.N)) &&
    ((runP P ONES lt Dig).2 && Nat.beq (runP P ONES lt Dig).1.a TA && Nat.beq (runP P ONES lt Dig).1.c TC &&
      Nat.beq (runP P ONES lt Dig).1.z TZ &&
      cond kind (Nat.beq (runP P ONES lt Dig).1.b TB) (Nat.beq (runP P ONES lt Dig).1.d TD))

end BipartiteDD.LeanAll.HaarSwar2

namespace BipartiteDD.LeanAll.HaarSL2

open BipartiteDD.LeanAll.HaarSwar2

/-- The inverse letter, in `Nat`. -/
def invLet (p n : Nat) (l : Let) : Let := ⟨l.h, (p - l.f) % p, (p - l.g) % p, l.e, (n - l.zw) % n⟩

/-- Batch `b`: `true` for the batches with `c = 0`. -/
def kindB (p b : Nat) : Bool := Nat.ble (p * (p - 1)) b

/-- The fixed upper-left entry of batch `b`. -/
def aB (p b : Nat) : Nat := cond (kindB p b) (b - p * (p - 1) + 1) (b / (p - 1))

/-- The fixed lower-left entry of batch `b`. -/
def cB (p b : Nat) : Nat := cond (kindB p b) 0 (b % (p - 1) + 1)

end BipartiteDD.LeanAll.HaarSL2

namespace BipartiteDD.LeanAll.Core

/-- `Swar.blk`: `Σ_{d < p} 2 ^ (w n d) * g d`. -/
def blk (w n : Nat) (g : Nat → Nat) (p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun d acc => acc + 2 ^ (w * n * d) * g d) p

/-- `(2 ^ (w N) - 1) / (2 ^ w - 1)`: `N` fields of `w` bits, each `1` (`Swar.pkF_one_eq`). -/
def onesC (w N : Nat) : Nat := (2 ^ (w * N) - 1) / (2 ^ w - 1)

end BipartiteDD.LeanAll.Core
