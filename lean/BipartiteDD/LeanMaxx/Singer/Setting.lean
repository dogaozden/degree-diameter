import BipartiteDD.SingerC.Core
import Mathlib.FieldTheory.Finite.GaloisField

/-! A general existence lemma for `SingerC.Setting`.

For an odd prime `p` and `e ≥ 1`, the field `GaloisField p (4 * e)` has `(p ^ e) ^ 4` elements,
and its unit group is cyclic (Mathlib: `IsCyclic`). A generator `g` of that group gives a
`Setting` with `q = p ^ e`. This is the construction behind `SingerC.Regular5440.setting13`,
with `13` replaced by `p` and `1` by `e`. -/

namespace BipartiteDD.LeanMaxx.Singer

open BipartiteDD.SingerC

variable (p : ℕ) [Fact p.Prime]

/-- Mathlib gives `GaloisField p n` only a `Finite` instance; `Setting` needs a `Fintype`. -/
noncomputable instance galoisFintype (n : ℕ) : Fintype (GaloisField p n) := Fintype.ofFinite _

/-- The Singer setting over `GaloisField p (4 * e)`, for odd `p` and `e ≥ 1`. The element `g` is a
generator of the cyclic group of units, so it has order `q ^ 4 - 1`. -/
noncomputable def setting (hodd : Odd p) (e : ℕ) (he : 1 ≤ e) :
    Setting (GaloisField p (4 * e)) p where
  e := e
  odd_p := hodd
  card_eq := by
    rw [Fintype.card_eq_nat_card, GaloisField.card p (4 * e) (by omega)]
    ring
  g := ((IsCyclic.exists_generator (α := (GaloisField p (4 * e))ˣ)).choose : (GaloisField p (4 * e))ˣ)
  orderOf_g := by
    have hg := (IsCyclic.exists_generator (α := (GaloisField p (4 * e))ˣ)).choose_spec
    rw [orderOf_units, orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units,
      Nat.card_eq_fintype_card]

/-- For every odd prime `p` and every `e ≥ 1` there is a `SingerC.Setting` over a field of order
`(p ^ e) ^ 4`, with `q = p ^ e`. -/
theorem setting_exists (hodd : Odd p) (e : ℕ) (he : 1 ≤ e) :
    ∃ S : Setting (GaloisField p (4 * e)) p, S.q = p ^ e :=
  ⟨setting p hodd e he, rfl⟩

end BipartiteDD.LeanMaxx.Singer
