import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Fintype.Card

/-! Regularity, part 2b: a perfect matching avoiding few forbidden pairs.

If two finite sets `X`, `Y` of the same size `n` are related by a "forbidden" relation in which every element
has at most `k` forbidden partners, and `2 k ≤ n`, then there is a bijection `X ≃ Y` that avoids every forbidden
pair. This is Hall's theorem: a set `S` of at most `n - k` elements has at least `n - k` allowed partners, and a
larger set has an allowed partner for every `y` (as at most `k < |S|` elements are forbidden for `y`). -/

namespace BipartiteDD.Regular

open Finset
open scoped Classical

theorem exists_matching_avoiding {X Y : Type*} [Fintype X] [Fintype Y] (f : X → Y → Prop) (k : ℕ)
    (hX : ∀ x, (univ.filter fun y => ¬ f x y).card ≤ k)
    (hY : ∀ y, (univ.filter fun x => ¬ f x y).card ≤ k)
    (hcard : Fintype.card X = Fintype.card Y) (h2k : 2 * k ≤ Fintype.card X) :
    ∃ g : X ≃ Y, ∀ x, f x (g x) := by
  let t : X → Finset Y := fun x => univ.filter fun y => f x y
  have hall : ∀ S : Finset X, S.card ≤ (S.biUnion t).card := by
    intro S
    by_cases hS : S.card ≤ Fintype.card Y - k
    · rcases S.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
      · simp
      · have h1 : (t x).card + (univ.filter fun y => ¬ f x y).card = Fintype.card Y := by
          rw [← card_univ]
          exact card_filter_add_card_filter_not _
        have h2 := hX x
        have h3 : (t x).card ≤ (S.biUnion t).card := card_le_card (subset_biUnion_of_mem t hx)
        omega
    · have hbig : S.biUnion t = univ := by
        refine eq_univ_of_forall fun y => ?_
        rw [mem_biUnion]
        by_contra hy
        push Not at hy
        have : S ⊆ univ.filter fun x => ¬ f x y := fun x hx => by
          simp only [mem_filter, mem_univ, true_and]
          intro hf
          exact hy x hx (by simp [t, hf])
        have h1 := card_le_card this
        have h2 := hY y
        omega
      rw [hbig, card_univ]
      exact (card_le_univ S).trans (le_of_eq hcard)
  obtain ⟨g, hg, hgt⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hall
  have hbij : Function.Bijective g := (Fintype.bijective_iff_injective_and_card g).2 ⟨hg, hcard⟩
  exact ⟨Equiv.ofBijective g hbij, fun x => by simpa [t] using hgt x⟩

end BipartiteDD.Regular
