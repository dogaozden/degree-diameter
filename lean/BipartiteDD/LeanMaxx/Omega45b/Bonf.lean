import Mathlib

/-!
# Lemma 4.3 (abstract part): Bonferroni's inequality for five sets and the three degenerate cases

For five finite sets `c 0, …, c 4` (the sets `C_y = {x : dist t x = 6, dist y x ≤ 4}` of the five centres):

* `bonf3`: `|⋃ cᵢ| + S₂ ≤ S₁ + S₃` (Bonferroni's inequality truncated after the triple sums);
* `union_bound`: if every `|cᵢ| ≤ 2401`, every pair that is not a "special pair" overlaps in `≥ 336` points,
  every triple that is not a "special triple" overlaps in `≤ 64` points, and fewer than `4` of the fifteen
  "closeness bits" (the five `cT i`, the ten `cl i j`) are set, then `|⋃ cᵢ| ≤ 9621`.

A *special pair* `(i, j)` is one with `cT i`, `cT j`, `cl i j` all set, a *special triple* one with the three
`cl` bits set. Three set bits cannot make two special objects (two special pairs need `≥ 5` bits, a special pair
and a special triple `≥ 5`, two special triples `≥ 5`), so with `≤ 3` bits at most one pair or triple is special;
the numbers `336` (pair overlap, Lemma 4.1), `64 = (q+1)²` (triple overlap) and `12005 = 5 · 2401` give
`12005 - (S₂ - S₃) ≤ 9621`. The note's table of 17 types is not needed for the `k = 4` version of Lemma 4.3.
-/

namespace BipartiteDD.LeanMaxx.Omega45b

open Finset

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- Pointwise Bonferroni (level 3) for five events. -/
theorem pw (b0 b1 b2 b3 b4 : Bool) :
    (b0 || b1 || b2 || b3 || b4).toNat +
      ((b0 && b1).toNat + (b0 && b2).toNat + (b0 && b3).toNat + (b0 && b4).toNat + (b1 && b2).toNat +
        (b1 && b3).toNat + (b1 && b4).toNat + (b2 && b3).toNat + (b2 && b4).toNat + (b3 && b4).toNat) ≤
    (b0.toNat + b1.toNat + b2.toNat + b3.toNat + b4.toNat) +
      ((b0 && b1 && b2).toNat + (b0 && b1 && b3).toNat + (b0 && b1 && b4).toNat +
        (b0 && b2 && b3).toNat + (b0 && b2 && b4).toNat + (b0 && b3 && b4).toNat +
        (b1 && b2 && b3).toNat + (b1 && b2 && b4).toNat + (b1 && b3 && b4).toNat +
        (b2 && b3 && b4).toNat) := by
  revert b0 b1 b2 b3 b4
  decide

theorem card_eq_sum_toNat (s : Finset U) : s.card = ∑ x : U, (decide (x ∈ s)).toNat := by
  have : ∀ x : U, (decide (x ∈ s)).toNat = if x ∈ s then 1 else 0 := fun x => by
    by_cases h : x ∈ s <;> simp [h]
  simp_rw [this]
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
  rfl

/-- **Bonferroni's inequality for five sets**, truncated after the triple sums. -/
theorem bonf3 (c : Fin 5 → Finset U) :
    (c 0 ∪ c 1 ∪ c 2 ∪ c 3 ∪ c 4).card +
      ((c 0 ∩ c 1).card + (c 0 ∩ c 2).card + (c 0 ∩ c 3).card + (c 0 ∩ c 4).card + (c 1 ∩ c 2).card +
        (c 1 ∩ c 3).card + (c 1 ∩ c 4).card + (c 2 ∩ c 3).card + (c 2 ∩ c 4).card + (c 3 ∩ c 4).card) ≤
    ((c 0).card + (c 1).card + (c 2).card + (c 3).card + (c 4).card) +
      ((c 0 ∩ c 1 ∩ c 2).card + (c 0 ∩ c 1 ∩ c 3).card + (c 0 ∩ c 1 ∩ c 4).card +
        (c 0 ∩ c 2 ∩ c 3).card + (c 0 ∩ c 2 ∩ c 4).card + (c 0 ∩ c 3 ∩ c 4).card +
        (c 1 ∩ c 2 ∩ c 3).card + (c 1 ∩ c 2 ∩ c 4).card + (c 1 ∩ c 3 ∩ c 4).card +
        (c 2 ∩ c 3 ∩ c 4).card) := by
  simp only [card_eq_sum_toNat, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x _ => ?_
  have := pw (decide (x ∈ c 0)) (decide (x ∈ c 1)) (decide (x ∈ c 2)) (decide (x ∈ c 3)) (decide (x ∈ c 4))
  have e1 : ∀ s t : Finset U, ∀ x, decide (x ∈ s ∩ t) = (decide (x ∈ s) && decide (x ∈ t)) := by
    intro s t x; simp [Finset.mem_inter]
  have e2 : ∀ s t : Finset U, ∀ x, decide (x ∈ s ∪ t) = (decide (x ∈ s) || decide (x ∈ t)) := by
    intro s t x; simp [Finset.mem_union]
  simp only [e1, e2]
  exact this

/-- Group inequalities: a pair `p` together with the triples `t` whose first pair it is. -/
theorem grp1 (p t s u : ℕ) (hp : 336 ≤ p + 336 * s) (ht : t ≤ 64 + 2337 * u) (hc : t ≤ p)
    (_hS : s + u ≤ 1) : t + 336 ≤ p + 336 * s + 272 * u + 64 := by omega

theorem grp2 (p t1 t2 s u1 u2 : ℕ) (hp : 336 ≤ p + 336 * s) (h1 : t1 ≤ 64 + 2337 * u1)
    (h2 : t2 ≤ 64 + 2337 * u2) (c1 : t1 ≤ p) (c2 : t2 ≤ p) (hS : s + u1 + u2 ≤ 1) :
    t1 + t2 + 336 ≤ p + 336 * s + 272 * (u1 + u2) + 128 := by omega

theorem grp3 (p t1 t2 t3 s u1 u2 u3 : ℕ) (hp : 336 ≤ p + 336 * s) (h1 : t1 ≤ 64 + 2337 * u1)
    (h2 : t2 ≤ 64 + 2337 * u2) (h3 : t3 ≤ 64 + 2337 * u3) (c1 : t1 ≤ p) (c2 : t2 ≤ p) (c3 : t3 ≤ p)
    (hS : s + u1 + u2 + u3 ≤ 1) :
    t1 + t2 + t3 + 336 ≤ p + 336 * s + 272 * (u1 + u2 + u3) + 192 := by omega

set_option maxHeartbeats 1000000 in
/-- The arithmetic of the three degenerate cases (at most one special pair or triple). Each triple is
assigned to its first pair. -/
theorem numeric
  (p01 p02 p03 p04 p12 p13 p14 p23 p24 p34 : ℕ)
  (t012 t013 t014 t023 t024 t034 t123 t124 t134 t234 : ℕ)
  (s01 s02 s03 s04 s12 s13 s14 s23 s24 s34 : ℕ)
  (u012 u013 u014 u023 u024 u034 u123 u124 u134 u234 : ℕ)
  (hS : s01+s02+s03+s04+s12+s13+s14+s23+s24+s34+u012+u013+u014+u023+u024+u034+u123+u124+u134+u234 ≤ 1)
  (hp01 : 336 ≤ p01 + 336*s01) (hp02 : 336 ≤ p02 + 336*s02) (hp03 : 336 ≤ p03 + 336*s03)
  (hp04 : 336 ≤ p04 + 336*s04) (hp12 : 336 ≤ p12 + 336*s12) (hp13 : 336 ≤ p13 + 336*s13)
  (hp14 : 336 ≤ p14 + 336*s14) (hp23 : 336 ≤ p23 + 336*s23) (hp24 : 336 ≤ p24 + 336*s24)
  (hp34 : 336 ≤ p34 + 336*s34)
  (ht012 : t012 ≤ 64 + 2337*u012) (ht013 : t013 ≤ 64 + 2337*u013) (ht014 : t014 ≤ 64 + 2337*u014)
  (ht023 : t023 ≤ 64 + 2337*u023) (ht024 : t024 ≤ 64 + 2337*u024) (ht034 : t034 ≤ 64 + 2337*u034)
  (ht123 : t123 ≤ 64 + 2337*u123) (ht124 : t124 ≤ 64 + 2337*u124) (ht134 : t134 ≤ 64 + 2337*u134)
  (ht234 : t234 ≤ 64 + 2337*u234)
  (c012 : t012 ≤ p01) (c013 : t013 ≤ p01) (c014 : t014 ≤ p01)
  (c023 : t023 ≤ p02) (c024 : t024 ≤ p02) (c034 : t034 ≤ p03)
  (c123 : t123 ≤ p12) (c124 : t124 ≤ p12) (c134 : t134 ≤ p13) (c234 : t234 ≤ p23) :
  t012+t013+t014+t023+t024+t034+t123+t124+t134+t234 + 2384 ≤ p01+p02+p03+p04+p12+p13+p14+p23+p24+p34 := by
  have g01 := grp3 p01 t012 t013 t014 s01 u012 u013 u014 hp01 ht012 ht013 ht014 c012 c013 c014 (by omega)
  have g02 := grp2 p02 t023 t024 s02 u023 u024 hp02 ht023 ht024 c023 c024 (by omega)
  have g03 := grp1 p03 t034 s03 u034 hp03 ht034 c034 (by omega)
  have g12 := grp2 p12 t123 t124 s12 u123 u124 hp12 ht123 ht124 c123 c124 (by omega)
  have g13 := grp1 p13 t134 s13 u134 hp13 ht134 c134 (by omega)
  have g23 := grp1 p23 t234 s23 u234 hp23 ht234 c234 (by omega)
  have e0 : (s01 + s02 + s03 + s04 + s12 + s13 + s14 + s23 + s24 + s34) +
      (u012 + u013 + u014 + u023 + u024 + u034 + u123 + u124 + u134 + u234) ≤ 1 := by omega
  have e1 : 336 * (s01 + s02 + s03 + s04 + s12 + s13 + s14 + s23 + s24 + s34) +
      272 * (u012 + u013 + u014 + u023 + u024 + u034 + u123 + u124 + u134 + u234) ≤ 336 := by
    generalize s01 + s02 + s03 + s04 + s12 + s13 + s14 + s23 + s24 + s34 = A at e0 ⊢
    generalize u012 + u013 + u014 + u023 + u024 + u034 + u123 + u124 + u134 + u234 = B at e0 ⊢
    omega
  linarith

theorem special_le (a0 a1 a2 a3 a4 l01 l02 l03 l04 l12 l13 l14 l23 l24 l34 : Bool)
    (h : a0.toNat + a1.toNat + a2.toNat + a3.toNat + a4.toNat + l01.toNat + l02.toNat + l03.toNat +
      l04.toNat + l12.toNat + l13.toNat + l14.toNat + l23.toNat + l24.toNat + l34.toNat ≤ 3) :
    (a0 && a1 && l01).toNat + (a0 && a2 && l02).toNat + (a0 && a3 && l03).toNat + (a0 && a4 && l04).toNat +
      (a1 && a2 && l12).toNat + (a1 && a3 && l13).toNat + (a1 && a4 && l14).toNat +
      (a2 && a3 && l23).toNat + (a2 && a4 && l24).toNat + (a3 && a4 && l34).toNat +
      (l01 && l02 && l12).toNat + (l01 && l03 && l13).toNat + (l01 && l04 && l14).toNat +
      (l02 && l03 && l23).toNat + (l02 && l04 && l24).toNat + (l03 && l04 && l34).toNat +
      (l12 && l13 && l23).toNat + (l12 && l14 && l24).toNat + (l13 && l14 && l34).toNat +
      (l23 && l24 && l34).toNat ≤ 1 := by
  revert a0 a1 a2 a3 a4 l01 l02 l03 l04 l12 l13 l14 l23 l24 l34
  decide +kernel

theorem pair_fact (a b l : Bool) (p : ℕ) (h : ¬(a = true ∧ b = true ∧ l = true) → 336 ≤ p) :
    336 ≤ p + 336 * (a && b && l).toNat := by
  cases a <;> cases b <;> cases l <;> simp_all

theorem triple_fact (x y z : Bool) (t : ℕ) (h : ¬(x = true ∧ y = true ∧ z = true) → t ≤ 64)
    (h2 : t ≤ 2401) : t ≤ 64 + 2337 * (x && y && z).toNat := by
  cases x <;> cases y <;> cases z <;> simp_all

/-- **Lemma 4.3, abstract form** (`k = 4`): five sets of size `≤ 2401` such that pairs which are not special
overlap in `≥ 336` points and triples which are not special in `≤ 64` points, with fewer than four closeness bits
set, have a union of size `≤ 9621`. (`16807 - 9621 = 7186 ≥ 140 · 49 + 326`.) -/
theorem union_bound (c : Fin 5 → Finset U) (cT : Fin 5 → Bool) (cl : Fin 5 → Fin 5 → Bool)
    (hsize : ∀ i, (c i).card ≤ 2401)
    (hpair : ∀ i j, i < j → ¬(cT i = true ∧ cT j = true ∧ cl i j = true) → 336 ≤ (c i ∩ c j).card)
    (htri : ∀ i j k, i < j → j < k → ¬(cl i j = true ∧ cl i k = true ∧ cl j k = true) →
      (c i ∩ c j ∩ c k).card ≤ 64)
    (hT : (cT 0).toNat + (cT 1).toNat + (cT 2).toNat + (cT 3).toNat + (cT 4).toNat + (cl 0 1).toNat +
      (cl 0 2).toNat + (cl 0 3).toNat + (cl 0 4).toNat + (cl 1 2).toNat + (cl 1 3).toNat + (cl 1 4).toNat +
      (cl 2 3).toNat + (cl 2 4).toNat + (cl 3 4).toNat ≤ 3) :
    (c 0 ∪ c 1 ∪ c 2 ∪ c 3 ∪ c 4).card ≤ 9621 := by
  have hb := bonf3 c
  have hS := special_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hT
  have sz : ∀ i j k : Fin 5, (c i ∩ c j ∩ c k).card ≤ 2401 := fun i j k =>
    (Finset.card_le_card (fun x hx => (Finset.mem_inter.1 (Finset.mem_inter.1 hx).1).1)).trans (hsize i)
  have sub1 : ∀ i j k : Fin 5, (c i ∩ c j ∩ c k).card ≤ (c i ∩ c j).card := fun i j k =>
    Finset.card_le_card Finset.inter_subset_left
  have := numeric (c 0 ∩ c 1).card (c 0 ∩ c 2).card (c 0 ∩ c 3).card (c 0 ∩ c 4).card (c 1 ∩ c 2).card
    (c 1 ∩ c 3).card (c 1 ∩ c 4).card (c 2 ∩ c 3).card (c 2 ∩ c 4).card (c 3 ∩ c 4).card
    (c 0 ∩ c 1 ∩ c 2).card (c 0 ∩ c 1 ∩ c 3).card (c 0 ∩ c 1 ∩ c 4).card (c 0 ∩ c 2 ∩ c 3).card
    (c 0 ∩ c 2 ∩ c 4).card (c 0 ∩ c 3 ∩ c 4).card (c 1 ∩ c 2 ∩ c 3).card (c 1 ∩ c 2 ∩ c 4).card
    (c 1 ∩ c 3 ∩ c 4).card (c 2 ∩ c 3 ∩ c 4).card
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hS
    (pair_fact _ _ _ _ (hpair 0 1 (by decide))) (pair_fact _ _ _ _ (hpair 0 2 (by decide)))
    (pair_fact _ _ _ _ (hpair 0 3 (by decide))) (pair_fact _ _ _ _ (hpair 0 4 (by decide)))
    (pair_fact _ _ _ _ (hpair 1 2 (by decide))) (pair_fact _ _ _ _ (hpair 1 3 (by decide)))
    (pair_fact _ _ _ _ (hpair 1 4 (by decide))) (pair_fact _ _ _ _ (hpair 2 3 (by decide)))
    (pair_fact _ _ _ _ (hpair 2 4 (by decide))) (pair_fact _ _ _ _ (hpair 3 4 (by decide)))
    (triple_fact _ _ _ _ (htri 0 1 2 (by decide) (by decide)) (sz _ _ _))
    (triple_fact _ _ _ _ (htri 0 1 3 (by decide) (by decide)) (sz _ _ _))
    (triple_fact _ _ _ _ (htri 0 1 4 (by decide) (by decide)) (sz _ _ _))
    (triple_fact _ _ _ _ (htri 0 2 3 (by decide) (by decide)) (sz _ _ _))
    (triple_fact _ _ _ _ (htri 0 2 4 (by decide) (by decide)) (sz _ _ _))
    (triple_fact _ _ _ _ (htri 0 3 4 (by decide) (by decide)) (sz _ _ _))
    (triple_fact _ _ _ _ (htri 1 2 3 (by decide) (by decide)) (sz _ _ _))
    (triple_fact _ _ _ _ (htri 1 2 4 (by decide) (by decide)) (sz _ _ _))
    (triple_fact _ _ _ _ (htri 1 3 4 (by decide) (by decide)) (sz _ _ _))
    (triple_fact _ _ _ _ (htri 2 3 4 (by decide) (by decide)) (sz _ _ _))
    (sub1 0 1 2) (sub1 0 1 3) (sub1 0 1 4) (sub1 0 2 3) (sub1 0 2 4) (sub1 0 3 4)
    (sub1 1 2 3) (sub1 1 2 4) (sub1 1 3 4) (sub1 2 3 4)
  have h0 := hsize 0
  have h1 := hsize 1
  have h2 := hsize 2
  have h3 := hsize 3
  have h4 := hsize 4
  omega

end BipartiteDD.LeanMaxx.Omega45b
