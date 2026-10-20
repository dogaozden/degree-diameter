import BipartiteDD.SingerC.W3Lines

/-! Corollary C1, step 4 (work in progress): the regular spread `{x · L : x ≠ 0}` of W(3,q). -/

namespace BipartiteDD.SingerC

open Module Projectivization

namespace Setting

variable {K : Type*} [Field K] [Fintype K] {p : ℕ} [Fact p.Prime] [CharP K p]
variable (S : Setting K p)

/-- `L = GF(q²)` as an `F`-submodule of `K`. -/
def Lsub : Submodule S.F K where
  carrier := {z | z ∈ S.L}
  add_mem' ha hb := S.L.add_mem ha hb
  zero_mem' := S.L.zero_mem
  smul_mem' c z hz := by
    show (c : K) * z ∈ S.L
    exact S.L.mul_mem (S.F_le_L c.2) hz

theorem mem_Lsub {z : K} : z ∈ S.Lsub ↔ z ∈ S.L := Iff.rfl

/-- Multiplication by `x`, as an `F`-linear map. -/
def mulL (x : K) : K →ₗ[S.F] K where
  toFun z := x * z
  map_add' z w := mul_add x z w
  map_smul' c z := by
    show x * ((c : K) * z) = (c : K) * (x * z)
    ring

/-- The spread element `x · L`. -/
def spreadSub (x : K) : Submodule S.F K := S.Lsub.map (S.mulL x)

theorem mem_spreadSub {x z : K} : z ∈ S.spreadSub x ↔ ∃ l ∈ S.L, x * l = z := by
  unfold spreadSub
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨l, hl, hlz⟩
    exact ⟨l, hl, hlz⟩
  · rintro ⟨l, hl, hlz⟩
    exact ⟨l, hl, hlz⟩

/-- `finrank` from the cardinality: `|W| = q ^ n` forces `dim W = n`. -/
theorem finrank_of_natCard (W : Submodule S.F K) (n : ℕ) (h : Nat.card W = S.q ^ n) :
    finrank S.F W = n := by
  classical
  have := Fintype.ofFinite W
  have hF : Fintype.card S.F = S.q := by rw [← Nat.card_eq_fintype_card]; exact S.natCard_F
  have h1 := Module.card_eq_pow_finrank (K := S.F) (V := W)
  rw [← Nat.card_eq_fintype_card, h, hF] at h1
  exact (Nat.pow_right_injective (S.one_lt_q : 2 ≤ S.q) h1).symm

theorem finrank_Lsub : finrank S.F S.Lsub = 2 := by
  apply S.finrank_of_natCard
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun z => S.mem_Lsub)), S.natCard_L]

theorem mulL_injective {x : K} (hx : x ≠ 0) : Function.Injective (S.mulL x) :=
  fun a b h => mul_left_cancel₀ hx h

theorem finrank_spreadSub {x : K} (hx : x ≠ 0) : finrank S.F (S.spreadSub x) = 2 :=
  ((S.Lsub.equivMapOfInjective (S.mulL x) (S.mulL_injective hx)).finrank_eq.symm).trans
    S.finrank_Lsub

/-- For `l, l' ∈ L`: `B(x l, x l') = 0`. -/
theorem B_spread (x : K) {l l' : K} (hl : l ∈ S.L) (hl' : l' ∈ S.L) :
    S.B (x * l) (x * l') = 0 := by
  have hl1 : l ^ S.q ^ 2 = l := S.mem_L.mp hl
  have hl2 : l' ^ S.q ^ 2 = l' := S.mem_L.mp hl'
  have hx4 : (x ^ S.q ^ 2) ^ S.q ^ 2 = x := by
    rw [← pow_mul, show S.q ^ 2 * S.q ^ 2 = S.q ^ 4 by ring, S.pow_card]
  unfold B
  apply S.tr4_eq_zero_of_conj_neg
  simp only [mul_pow, S.d_pow_q_sq, hx4, hl1, hl2]
  ring

theorem TI_spreadSub (x : K) : ∀ u ∈ S.spreadSub x, ∀ u' ∈ S.spreadSub x, S.B u u' = 0 := by
  intro u hu u' hu'
  obtain ⟨l, hl, rfl⟩ := (S.mem_spreadSub).mp hu
  obtain ⟨l', hl', rfl⟩ := (S.mem_spreadSub).mp hu'
  exact S.B_spread x hl hl'

/-- The spread line `x · L`, for `x ≠ 0`. -/
def spreadLine {x : K} (hx : x ≠ 0) : S.TILine :=
  ⟨S.spreadSub x, S.finrank_spreadSub hx, S.TI_spreadSub x⟩

/-- A spread line: `x · L` for some `x ≠ 0`. -/
def IsSpread (l : S.TILine) : Prop := ∃ x : K, ∃ hx : x ≠ 0, l.1 = S.spreadSub x

/-- If `z ∈ x · L` with `z ≠ 0`, then `z · L = x · L`. -/
theorem spreadSub_eq_of_mem {x z : K} (hz : z ∈ S.spreadSub x) (hz0 : z ≠ 0) :
    S.spreadSub z = S.spreadSub x := by
  obtain ⟨l0, hl0, rfl⟩ := (S.mem_spreadSub).mp hz
  have hl0' : l0 ≠ 0 := fun h => hz0 (by rw [h, mul_zero])
  ext w
  rw [S.mem_spreadSub, S.mem_spreadSub]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l0 * l, S.L.mul_mem hl0 hl, by ring⟩
  · rintro ⟨l, hl, rfl⟩
    refine ⟨l0⁻¹ * l, S.L.mul_mem (S.L.inv_mem hl0) hl, ?_⟩
    rw [mul_assoc, ← mul_assoc l0, mul_inv_cancel₀ hl0', one_mul]

/-- A point lies on a line iff its representative does. -/
theorem pt_mem_iff (l : S.TILine) (x : ℙ S.F K) : x ∈ l ↔ x.rep ∈ l.1 := by
  show x.submodule ≤ l.1 ↔ _
  rw [Projectivization.submodule_eq, Submodule.span_singleton_le_iff_mem]

theorem rep_mem_spreadSub_self (x : ℙ S.F K) : x.rep ∈ S.spreadSub x.rep := by
  rw [S.mem_spreadSub]
  exact ⟨1, S.L.one_mem, mul_one _⟩

/-- Every point lies on the spread line through its representative. -/
theorem pt_mem_spreadLine (x : ℙ S.F K) : x ∈ S.spreadLine x.rep_nonzero := by
  rw [S.pt_mem_iff]
  exact S.rep_mem_spreadSub_self x

/-- Each point lies on at most one spread line. -/
theorem spread_unique {x : ℙ S.F K} {l l' : S.TILine} (hl : S.IsSpread l) (hl' : S.IsSpread l')
    (hxl : x ∈ l) (hxl' : x ∈ l') : l = l' := by
  obtain ⟨a, _, ha⟩ := hl
  obtain ⟨b, _, hb⟩ := hl'
  rw [S.pt_mem_iff, ha] at hxl
  rw [S.pt_mem_iff, hb] at hxl'
  apply Subtype.ext
  rw [ha, hb, ← S.spreadSub_eq_of_mem hxl x.rep_nonzero,
    S.spreadSub_eq_of_mem hxl' x.rep_nonzero]

end Setting

end BipartiteDD.SingerC
