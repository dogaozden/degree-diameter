import BipartiteDD.Doubling.Levels
import Mathlib.Basic.Finite.Sum

/-! Group Doubling, part 4: the degree bound in the levelled doubling.

The neighbours of a version `u^s` are the versions `v^t` with `u ~ v` and `s`, `t` prefix-comparable.
A neighbour `v` of height at most `h u` has exactly one such `t` (the prefix of `s`), and a neighbour of
height `h u + 1` has `m` of them (`s` followed by any letter). By (a) there is no neighbour of height
more than `h u + 1`, and by (a), (b) at most one neighbour is higher than `u`; so the degree rises by at most
`m - 1`. The neighbourhood is shown to be in the range of a map from `N(u) ⊕ Fin (m - 1)`. -/

namespace BipartiteDD.Doubling

open SimpleGraph
open scoped Classical

variable {V : Type*} {G : SimpleGraph V} {m : ℕ} {h : V → ℕ}

/-- A finite set inside the range of a map from a finite type has at most `Nat.card` of that type. -/
theorem ncard_le_of_subset_range' {W D : Type*} [Finite D] (N : Set W) (g : D → W)
    (hN : N ⊆ Set.range g) : N.ncard ≤ Nat.card D := by
  have h1 : (Set.range g).ncard ≤ Nat.card D := by
    rw [← Set.image_univ, ← Set.ncard_univ D]
    exact Set.ncard_image_le
  exact (Set.ncard_le_ncard hN (Set.finite_range g)).trans h1

/-- The string `s` of length `h u`, cut or padded with the letter `c` to length `h v`. -/
def extStr (u : V) (s : Fin (h u) → Fin m) (c : Fin m) (v : V) : Fin (h v) → Fin m :=
  fun i => if hi : (i : ℕ) < h u then s ⟨i, hi⟩ else c

/-- A string `t` of length `h v` agreeing with `s` is `s` cut or padded, as long as `t` is `c` beyond
the length of `s`. -/
theorem eq_extStr {u v : V} {s : Fin (h u) → Fin m} {t : Fin (h v) → Fin m} (hst : Agree s t)
    {c : Fin m} (hc : ∀ i : Fin (h v), ¬ (i : ℕ) < h u → t i = c) : t = extStr u s c v := by
  funext i
  by_cases hi : (i : ℕ) < h u
  · simp [extStr, hi, hst i hi i.2]
  · simp [extStr, hi, hc i hi]

/-- Degree bound: at most `Δ + (m - 1)`. Hypotheses: `hstep` is (a)'s `N(A_{i+1}) ⊆ A_i` (a neighbour
has height at most one more), and `hup` is (a)'s and (b)'s "at most one neighbour in the next level up". -/
theorem levelled_degree [Finite V] (hm : 0 < m) {Δ : ℕ} (hΔ : ∀ v, (G.neighborSet v).ncard ≤ Δ)
    (hstep : ∀ u v, G.Adj u v → h v ≤ h u + 1)
    (hup : ∀ u, {v | G.Adj u v ∧ h u < h v}.ncard ≤ 1) (x : Ver V m h) :
    ((levelled G m h).neighborSet x).ncard ≤ Δ + (m - 1) := by
  obtain ⟨u, s⟩ := x
  let v₀ : V := if hex : ∃ v, G.Adj u v ∧ h u < h v then hex.choose else u
  let g : (G.neighborSet u) ⊕ Fin (m - 1) → Ver V m h
    | .inl v => ⟨v.1, extStr u s ⟨0, hm⟩ v.1⟩
    | .inr j => ⟨v₀, extStr u s ⟨j.1 + 1, by have := j.2; omega⟩ v₀⟩
  have hsub : (levelled G m h).neighborSet ⟨u, s⟩ ⊆ Set.range g := by
    rintro ⟨v, t⟩ ⟨huv, hst⟩
    replace huv : G.Adj u v := huv
    replace hst : Agree s t := hst
    by_cases hv : h v ≤ h u
    · refine ⟨.inl ⟨v, huv⟩, ?_⟩
      show (⟨v, extStr u s ⟨0, hm⟩ v⟩ : Ver V m h) = ⟨v, t⟩
      congr 1
      refine (eq_extStr hst ?_).symm
      intro i hi
      have := i.2
      omega
    · have hlt : h u < h v := by omega
      have hv1 : h v = h u + 1 := by have := hstep u v huv; omega
      have hex : ∃ w, G.Adj u w ∧ h u < h w := ⟨v, huv, hlt⟩
      have hv0 : v₀ = v := by
        have hspec := hex.choose_spec
        have : v₀ = hex.choose := by simp [v₀, hex]
        rw [this]
        exact (Set.ncard_le_one_iff (Set.toFinite _)).1 (hup u) hspec ⟨huv, hlt⟩
      -- the letter after the prefix `s`
      have hi0 : h u < h v := hlt
      let c : Fin m := t ⟨h u, hi0⟩
      have ht : t = extStr u s c v := by
        refine eq_extStr hst ?_
        intro i hi
        have : (i : ℕ) = h u := by have := i.2; omega
        have : i = ⟨h u, hi0⟩ := Fin.ext this
        rw [this]
      by_cases hc0 : c.1 = 0
      · refine ⟨.inl ⟨v, huv⟩, ?_⟩
        show (⟨v, extStr u s ⟨0, hm⟩ v⟩ : Ver V m h) = ⟨v, t⟩
        have hc : c = ⟨0, hm⟩ := Fin.ext hc0
        rw [ht, hc]
      · have hcm : c.1 - 1 < m - 1 := by have := c.2; omega
        refine ⟨.inr ⟨c.1 - 1, hcm⟩, ?_⟩
        show (⟨v₀, extStr u s ⟨(c.1 - 1) + 1, _⟩ v₀⟩ : Ver V m h) = ⟨v, t⟩
        have hc : (⟨(c.1 - 1) + 1, by omega⟩ : Fin m) = c := Fin.ext (by simp only; omega)
        rw [hv0, hc, ← ht]
  have : Finite (G.neighborSet u) := Subtype.finite
  calc ((levelled G m h).neighborSet ⟨u, s⟩).ncard
      ≤ Nat.card ((G.neighborSet u) ⊕ Fin (m - 1)) := ncard_le_of_subset_range' _ g hsub
    _ = (G.neighborSet u).ncard + (m - 1) := by
        rw [Nat.card_sum, Nat.card_eq_fintype_card (α := Fin (m - 1)), Fintype.card_fin,
          Nat.card_coe_set_eq]
    _ ≤ Δ + (m - 1) := Nat.add_le_add_right (hΔ u) _

end BipartiteDD.Doubling
