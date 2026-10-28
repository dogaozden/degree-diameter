import BipartiteDD.LeanMaxx.Haarbound.Main
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Int.Interval

/-! Theorem 4.3 of `research/theorems/HAAR_D8_10.md` (§4.2): the abelianization bound.

If `|S| = Δ` and `H(G, S)` has diameter at most `D`, then `|G / G'| ≤ A(Δ, D)`, where `G' = [G, G]` and
`A(Δ, D)` counts the integer vectors `c ∈ ℤ^Δ` with `∑ c_i = ε` and `∑ |c_i| ≤ D - 1`, with
`ε = 1` for `D` even and `ε = 0` for `D` odd.

Proof (as in the note). Write `φ : G → G/G'` for the quotient map. An A-walk from `(e, A)` of length
`L` is a signed word in `S`: each step `(g, A) → (s g, B)` contributes `+s` and each step back contributes
`-s`. So the class of its endpoint is `∏_{s} φ(s)^{c_s}` for an exponent vector `c` with `∑ |c_s| ≤ L` and
`∑ c_s = [L odd]`. Every class of `G/G'` is the class of a far-side vertex (`exists_far_walk`), so the
exponent vectors with the right constraints already hit all of `G/G'`. -/

namespace BipartiteDD.LeanMaxx.HaarBound

open Finset SimpleGraph BipartiteDD.Haar

variable {G : Type*} [Group G]

/-- The letter of the edge `u — v` of `H(G, S)`: `h g⁻¹` for the edge between `inl g` and `inr h`. -/
def edgeLetter : G ⊕ G → G ⊕ G → G
  | Sum.inl g, Sum.inr h => h * g⁻¹
  | Sum.inr h, Sum.inl g => h * g⁻¹
  | _, _ => 1

theorem edgeLetter_mem {S : Finset G} {u v : G ⊕ G} (h : (haarGraph S).Adj u v) :
    edgeLetter u v ∈ S := by
  rcases u with g | h1 <;> rcases v with g' | h2
  · exact absurd h (haarGraph_not_adj_inl_inl S g g')
  · rw [haarGraph_adj_inl_inr] at h
    exact h
  · rw [haarGraph_adj_inr_inl] at h
    exact h
  · exact absurd h (haarGraph_not_adj_inr_inr S h1 h2)

/-- The abelian class of a vertex: `g` on the `A` side and `h` on the `B` side, mapped to `G/G'`. -/
def vq (x : G ⊕ G) : Abelianization G := Abelianization.of (Sum.elim id id x)

/-- `+1` on the `A` side and `-1` on the `B` side. -/
def sgn (x : G ⊕ G) : ℤ := if x.isLeft then 1 else -1

omit [Group G] in
theorem sgn_abs (x : G ⊕ G) : |sgn x| = 1 := by
  unfold sgn
  split_ifs <;> simp

theorem sgn_ne {S : Finset G} {a b : G ⊕ G} (h : (haarGraph S).Adj a b) : sgn b = -sgn a := by
  have hne := isLeft_ne_of_adj h
  unfold sgn
  cases ha : a.isLeft <;> cases hb : b.isLeft <;> simp_all

/-- The step relation: one edge multiplies the class by `φ(letter)^{sgn a}`. -/
theorem vq_step {S : Finset G} {a b : G ⊕ G} (h : (haarGraph S).Adj a b) :
    vq b = vq a * (Abelianization.of ((⟨edgeLetter a b, edgeLetter_mem h⟩ : S) : G)) ^ sgn a := by
  rcases a with g | g <;> rcases b with g' | g'
  · exact absurd h (haarGraph_not_adj_inl_inl S g g')
  · show Abelianization.of g' = Abelianization.of g * Abelianization.of (g' * g⁻¹) ^ (1 : ℤ)
    simp [map_mul, map_inv]
  · show Abelianization.of g' = Abelianization.of g * Abelianization.of (g * g'⁻¹) ^ (-1 : ℤ)
    simp [map_mul, map_inv]
  · exact absurd h (haarGraph_not_adj_inr_inr S g g')

/-- The class `∏_{s ∈ S} φ(s)^{e s}` of an exponent vector `e` on the letters of `S`. -/
def Phi (S : Finset G) (e : S → ℤ) : Abelianization G :=
  ∏ s : S, Abelianization.of (s : G) ^ e s

theorem Phi_zero (S : Finset G) : Phi S 0 = 1 := by
  simp [Phi]

theorem Phi_add_single [DecidableEq G] (S : Finset G) (e : S → ℤ) (a : S) (z : ℤ) :
    Phi S (e + Pi.single a z) = Phi S e * Abelianization.of (a : G) ^ z := by
  unfold Phi
  have hsplit : ∀ s : S, Abelianization.of (s : G) ^ ((e + (Pi.single a z : S → ℤ)) s)
      = Abelianization.of (s : G) ^ e s * Abelianization.of (s : G) ^ ((Pi.single a z : S → ℤ) s) :=
    fun s => by rw [Pi.add_apply, zpow_add]
  simp only [hsplit, Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_eq_single a]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ a) h

omit [Group G] in
theorem sum_add_single [DecidableEq G] (S : Finset G) (e : S → ℤ) (a : S) (z : ℤ) :
    ∑ s : S, (e + (Pi.single a z : S → ℤ)) s = ∑ s : S, e s + z := by
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ a) h

omit [Group G] in
theorem sum_abs_add_single [DecidableEq G] (S : Finset G) (e : S → ℤ) (a : S) (z : ℤ) :
    ∑ s : S, |(e + (Pi.single a z : S → ℤ)) s| ≤ ∑ s : S, |e s| + |z| := by
  calc ∑ s : S, |(e + (Pi.single a z : S → ℤ)) s| ≤ ∑ s : S, (|e s| + |(Pi.single a z : S → ℤ) s|) :=
        Finset.sum_le_sum fun s _ => by
          rw [Pi.add_apply]
          exact abs_add_le _ _
    _ = ∑ s : S, |e s| + |z| := by
        rw [Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_eq_single a]
        · simp
        · intro b _ hb
          simp [Pi.single_apply, hb]
        · intro h
          exact absurd (Finset.mem_univ a) h

/-- Walk invariant. A walk `p` from `u` to `w` has an exponent vector `e` on the letters with
`∑ |e| ≤ length`, signed sum `sgn u · [length odd]`, and `vq w = vq u · Φ(e)`. -/
theorem walk_exists [DecidableEq G] {S : Finset G} {u w : G ⊕ G} (p : (haarGraph S).Walk u w) :
    ∃ e : S → ℤ, ∑ s, |e s| ≤ (p.length : ℤ) ∧
      ∑ s, e s = sgn u * (if Odd p.length then 1 else 0) ∧ vq w = vq u * Phi S e := by
  induction p with
  | nil => exact ⟨0, by simp, by simp, by simp [Phi_zero]⟩
  | @cons a b c h p ih =>
    obtain ⟨e, hbound, hsum, hval⟩ := ih
    refine ⟨e + (Pi.single ⟨edgeLetter a b, edgeLetter_mem h⟩ (sgn a) : S → ℤ), ?_, ?_, ?_⟩
    · refine (sum_abs_add_single S e _ (sgn a)).trans ?_
      rw [sgn_abs]
      simp only [SimpleGraph.Walk.length_cons]
      push_cast
      linarith
    · rw [sum_add_single, hsum, sgn_ne h]
      simp only [SimpleGraph.Walk.length_cons, Nat.odd_add_one]
      by_cases hL : Odd p.length <;> simp [hL]
    · rw [hval, vq_step h, Phi_add_single]
      simp only [mul_assoc, mul_comm, mul_left_comm]

/-- Every class of `G / G'` is `φ(x)` for some `x`. -/
theorem of_surj (q : Abelianization G) : ∃ x : G, Abelianization.of x = q := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨x, rfl⟩

/-- **Theorem 4.3 (abelianization bound).** If `|S| = Δ` and `H(G, S)` has diameter at most `D`, then
`|G / G'| ≤ A(Δ, D)`, where `A(Δ, D)` counts `c ∈ ℤ^Δ` with `∑ c_i = ε` and `∑ |c_i| ≤ D - 1`, and
`ε = 1` if `D` is even, `ε = 0` if `D` is odd. -/
theorem abelianization_card_le {Δ D : ℕ} (S : Finset G) (hS : S.card = Δ)
    (hdiam : (haarGraph S).ediam ≤ D) :
    Nat.card (Abelianization G) ≤
      Nat.card {c : Fin Δ → ℤ // ∑ i, c i = (if D % 2 = 0 then 1 else 0) ∧ ∑ i, |c i| ≤ (D : ℤ) - 1} := by
  classical
  -- surjectivity of the exponent vectors onto `G / G'`
  have hsurj : Function.Surjective (fun c : {e : S → ℤ //
      ∑ s, e s = (if D % 2 = 0 then 1 else 0) ∧ ∑ s, |e s| ≤ (D : ℤ) - 1} => Phi S c.1) := by
    intro q
    obtain ⟨x, rfl⟩ := of_surj q
    obtain ⟨m, hmD, hmod, hm⟩ := exists_far_walk S hdiam x
    obtain ⟨p, hp⟩ := exists_walk_of_edist_eq_coe hm
    obtain ⟨e, hbound, hsum, hval⟩ := walk_exists p
    rw [hp] at hbound hsum
    have hvq : vq (farVertex D x) = Abelianization.of x := by
      unfold farVertex vq
      split_ifs <;> rfl
    have hinl : vq (Sum.inl (1 : G)) = 1 := by simp [vq]
    have hsg : sgn (Sum.inl (1 : G)) = 1 := by simp [sgn]
    rw [hvq, hinl, one_mul] at hval
    rw [hsg, one_mul] at hsum
    have hodd : Odd m ↔ D % 2 = 0 := by
      rw [Nat.odd_iff]
      constructor <;> intro h <;> omega
    have hsumε : ∑ s, e s = (if D % 2 = 0 then 1 else 0) := by
      rw [hsum]
      by_cases h : Odd m
      · rw [if_pos h, if_pos (hodd.mp h)]
      · rw [if_neg h, if_neg (fun h' => h (hodd.mpr h'))]
    have hbd : ∑ s, |e s| ≤ (D : ℤ) - 1 := hbound.trans (by omega)
    exact ⟨⟨e, hsumε, hbd⟩, hval.symm⟩
  -- finitely many exponent vectors with `∑ |e| ≤ D - 1`
  have hfin : Finite {e : S → ℤ //
      ∑ s, e s = (if D % 2 = 0 then 1 else 0) ∧ ∑ s, |e s| ≤ (D : ℤ) - 1} := by
    have hT : (Set.univ.pi fun _ : S => Set.Icc (-(D : ℤ)) D).Finite :=
      Set.Finite.pi fun _ => Set.finite_Icc _ _
    have hsub : {e : S → ℤ | ∑ s, e s = (if D % 2 = 0 then 1 else 0) ∧
        ∑ s, |e s| ≤ (D : ℤ) - 1} ⊆ Set.univ.pi fun _ : S => Set.Icc (-(D : ℤ)) D := by
      intro e he
      have he' := he.2
      intro s _
      have h1 : |e s| ≤ ∑ t, |e t| :=
        Finset.single_le_sum (f := fun t => |e t|) (fun t _ => abs_nonneg _) (Finset.mem_univ s)
      have h2 := abs_le.mp (h1.trans he')
      exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
    exact (hT.subset hsub).to_subtype
  -- transfer from the letters of `S` to `Fin Δ`
  have hcard : Fintype.card S = Δ := by rw [Fintype.card_coe, hS]
  let σ : S ≃ Fin Δ := Fintype.equivFinOfCardEq hcard
  have hequiv : Nat.card {e : S → ℤ //
      ∑ s, e s = (if D % 2 = 0 then 1 else 0) ∧ ∑ s, |e s| ≤ (D : ℤ) - 1} =
      Nat.card {c : Fin Δ → ℤ // ∑ i, c i = (if D % 2 = 0 then 1 else 0) ∧ ∑ i, |c i| ≤ (D : ℤ) - 1} := by
    refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.arrowCongr σ (Equiv.refl ℤ)) ?_)
    intro e
    have h1 : ∑ i, e (σ.symm i) = ∑ s, e s := Equiv.sum_comp σ.symm e
    have h2 : ∑ i, |e (σ.symm i)| = ∑ s, |e s| := Equiv.sum_comp σ.symm (fun s => |e s|)
    simp only [Equiv.arrowCongr_apply, Equiv.refl_apply, Function.comp_apply, h1, h2]
  calc Nat.card (Abelianization G) ≤ Nat.card {e : S → ℤ //
        ∑ s, e s = (if D % 2 = 0 then 1 else 0) ∧ ∑ s, |e s| ≤ (D : ℤ) - 1} :=
        Nat.card_le_card_of_surjective _ hsurj
    _ = _ := hequiv

end BipartiteDD.LeanMaxx.HaarBound
