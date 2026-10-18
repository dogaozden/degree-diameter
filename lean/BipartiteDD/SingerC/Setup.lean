import Mathlib

/-! Setup for Proposition C (Singer-orbit 2-ovoids of W(3,q)).

`K` is a finite field of characteristic `p` with `q = p ^ e` elements of the base field `F`
and `q ^ 4` elements in total. `F` and `L` are the fixed fields of `x ↦ x ^ q` and `x ↦ x ^ (q ^ 2)`.
No Galois theory is used: traces and conjugates are explicit Frobenius sums. -/

namespace BipartiteDD.SingerC

open Finset

section Fixed

variable {K : Type*} [Field K] [Fintype K]
variable {p : ℕ} [hp : Fact p.Prime] [CharP K p]

/-- `{x | x ^ p ^ k = x}` as a subfield of `K`, for odd `p`. -/
def fixSub (hodd : Odd p) (k : ℕ) : Subfield K where
  carrier := {x | x ^ p ^ k = x}
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq] at *
    rw [mul_pow, hx, hy]
  one_mem' := by simp
  add_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq] at *
    rw [add_pow_expChar_pow, hx, hy]
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    exact zero_pow (pow_ne_zero _ hp.out.ne_zero)
  neg_mem' {x} hx := by
    simp only [Set.mem_ofPred_eq] at *
    rw [(hodd.pow).neg_pow, hx]
  inv_mem' {x} hx := by
    simp only [Set.mem_ofPred_eq] at *
    rw [inv_pow, hx]

omit [Fintype K] in
theorem mem_fixSub {hodd : Odd p} {k : ℕ} {x : K} : x ∈ fixSub hodd k ↔ x ^ p ^ k = x :=
  Iff.rfl

open Classical in
/-- If `m - 1` divides `|K| - 1` and `g` is a generator of `Kˣ`, then exactly `m` elements satisfy
`x ^ m = x`. -/
theorem card_pow_eq_self {g : K} {m : ℕ} (hg : orderOf g = Fintype.card K - 1) (hm : 1 < m)
    (hdvd : m - 1 ∣ Fintype.card K - 1) :
    (univ.filter (fun x : K => x ^ m = x)).card = m := by
  have hk : 0 < m - 1 := by omega
  have hle : m - 1 ≤ Fintype.card K - 1 := Nat.le_of_dvd (by have := Fintype.one_lt_card (α := K); omega) hdvd
  have hprim : IsPrimitiveRoot (g ^ ((Fintype.card K - 1) / (m - 1))) (m - 1) := by
    have h1 : IsPrimitiveRoot g (Fintype.card K - 1) := by
      rw [IsPrimitiveRoot.iff_orderOf]
      exact hg
    have hpos : (Fintype.card K - 1) / (m - 1) ≠ 0 :=
      (Nat.div_pos hle hk).ne'
    have h2 := h1.pow_of_dvd hpos (Nat.div_dvd_of_dvd hdvd)
    rwa [Nat.div_div_self hdvd (by omega)] at h2
  have hset : univ.filter (fun x : K => x ^ m = x) = insert 0 (Polynomial.nthRootsFinset (m - 1) (1 : K)) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_insert, Polynomial.mem_nthRootsFinset hk]
    constructor
    · intro hx
      by_cases h0 : x = 0
      · exact Or.inl h0
      · right
        apply mul_left_cancel₀ h0
        rw [mul_one, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ m)]
        exact hx
    · rintro (rfl | hx)
      · simp [zero_pow (by omega : m ≠ 0)]
      · have hm' : x ^ m = x * x ^ (m - 1) := by
          rw [← pow_succ']
          congr 1
          omega
        rw [hm', hx, mul_one]
  rw [hset, card_insert_of_notMem, hprim.card_nthRootsFinset]
  · omega
  · rw [Polynomial.mem_nthRootsFinset hk]
    simp [zero_pow (by omega : m - 1 ≠ 0)]

end Fixed

end BipartiteDD.SingerC
