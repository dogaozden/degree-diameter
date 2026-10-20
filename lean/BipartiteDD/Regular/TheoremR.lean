import BipartiteDD.Regular.Twin
import BipartiteDD.Regular.Completion

/-! Regularity, part 4: the abstract part of Theorem R (diameter 6, any diameter).

Let `r : α → β → Prop` be a bipartite graph with `|α| = n₂ < n₁ = |β|`, maximum degree at most `Δ` and diameter
at most `D`. Suppose `S ⊆ β` has `n₁ - n₂` elements, each of which has a *twin* (same neighbourhood) outside `S`
(equivalently, `S` takes at most `m - 1` vertices from each twin class of size `m`; see `htwin_of_classes`).

* By the twin lemma (`Twin`), deleting `S` does not increase any distance: the remaining graph, on `α ⊕ {b // b ∉ S}`
  with `n₂ + n₂` vertices, still has diameter at most `D`.
* The deficits of the remaining graph are the numbers `Δ - deg`. If each is at most `s` and the total deficit
  of the `α` side exceeds `2 s (Δ + s + 1)`, the completion lemma (`Completion`) adds cross edges to make every
  degree exactly `Δ`, without increasing the diameter.

So there is a `Δ`-regular bipartite graph of diameter at most `D` on `2 n₂` vertices. -/

namespace BipartiteDD.Regular

open Finset
open scoped Classical

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Deleting vertices of `β` can only lower the degree of a vertex of `α`. -/
theorem degL_restrictR_le (r : α → β → Prop) (S : Set β) (a : α) : degL (restrictR r S) a ≤ degL r a :=
  Set.ncard_le_ncard_of_injOn (fun b => b.1) (fun b hb => hb) (fun b _ b' _ h => Subtype.ext h)
    (Set.toFinite _)

/-- A vertex of `β` that is not deleted keeps its degree. -/
theorem degR_restrictR (r : α → β → Prop) (S : Set β) (b : {b // b ∉ S}) :
    degR (restrictR r S) b = degR r b.1 := rfl

/-- The degree of `a` after deleting `S` is its old degree minus the number of deleted neighbours. -/
theorem degL_restrictR_add (r : α → β → Prop) (S : Finset β) (a : α) :
    degL (restrictR r (S : Set β)) a + (S.filter fun b => r a b).card = degL r a := by
  have h1 : degL (restrictR r (S : Set β)) a = (univ.filter fun b => r a b ∧ b ∉ S).card := by
    unfold degL restrictR
    have : {b : {b // b ∉ (S : Set β)} | r a b.1}.ncard = (Subtype.val '' {b : {b // b ∉ (S : Set β)} | r a b.1}).ncard :=
      (Set.ncard_image_of_injective _ Subtype.val_injective).symm
    rw [this, ← Set.ncard_coe_finset]
    congr 1
    ext b
    simp
  have h2 : degL r a = (univ.filter fun b => r a b).card := by
    unfold degL
    exact ncard_setOf_eq_card_filter _
  have h3 := card_filter_add_card_filter_not (s := univ.filter fun b => r a b) (fun b => b ∈ S)
  have e1 : ((univ.filter fun b => r a b).filter fun b => b ∈ S) = S.filter fun b => r a b := by
    ext b
    simp [and_comm]
  have e2 : ((univ.filter fun b => r a b).filter fun b => b ∉ S) = univ.filter fun b => r a b ∧ b ∉ S := by
    ext b
    simp
  rw [e1, e2] at h3
  omega

/-- The number of vertices of `β` outside the finset `S`. -/
theorem card_notMem_finset (S : Finset β) : Fintype.card {b : β // b ∉ (S : Set β)} + S.card = Fintype.card β := by
  have h1 : Fintype.card {b : β // b ∉ (S : Set β)} = (univ.filter fun b => b ∉ S).card := by
    rw [Fintype.card_subtype]
    simp
  have h2 := card_filter_add_card_filter_not (s := (univ : Finset β)) (fun b => b ∈ S)
  have h3 : (univ.filter fun b => b ∈ S) = S := by
    ext b
    simp
  rw [h3, card_univ] at h2
  omega

/-- **Theorem R, abstract part.** `r` is a bipartite graph with `n₂ = |α|` and `n₁ = |β|` vertices on its sides
and diameter at most `D`, with maximum degree at most `Δ`. The finset `S ⊆ β` has `n₁ - n₂` elements, each with a
twin outside `S`. After deleting `S`, every deficit `Δ - deg` is at most `s` and the total deficit of the `α`
side exceeds `2 s (Δ + s + 1)`. Then there is a `Δ`-regular bipartite graph of diameter at most `D` on `2 n₂`
vertices. -/
theorem regular_of_twins (r : α → β → Prop) (Δ s D : ℕ) (S : Finset β)
    (hS : Fintype.card α + S.card = Fintype.card β)
    (htwin : ∀ b ∈ (S : Set β), ∃ b' ∉ (S : Set β), ∀ a, r a b' ↔ r a b)
    (hdegα : ∀ a, degL r a ≤ Δ) (hdegβ : ∀ b, degR r b ≤ Δ)
    (hsα : ∀ a, Δ - degL (restrictR r S) a ≤ s)
    (hsβ : ∀ b : {b // b ∉ (S : Set β)}, Δ - degR (restrictR r (S : Set β)) b ≤ s)
    (hbig : 2 * s * (Δ + s + 1) < ∑ a, (Δ - degL (restrictR r (S : Set β)) a))
    (hD : (biGraph r).ediam ≤ D) :
    ∃ G : SimpleGraph (Fin (2 * Fintype.card α)), IsBipartiteRegDiam G Δ D := by
  have hcard : Fintype.card α = Fintype.card {b : β // b ∉ (S : Set β)} := by
    have := card_notMem_finset S
    omega
  exact exists_regular_completion_fin (restrictR r (S : Set β)) Δ s D
    (fun a => (degL_restrictR_le r _ a).trans (hdegα a))
    (fun b => by rw [degR_restrictR]; exact hdegβ _) hsα hsβ hcard hbig
    (ediam_restrict_le_of_le r (S : Set β) htwin hD)

/-- The same with twin classes: the vertices of `β` carry a class label `cls`, vertices of the same class have
the same neighbourhood, and `S` takes fewer than all the vertices of every class. -/
theorem regular_of_twin_classes {κ : Type*} [DecidableEq κ] (r : α → β → Prop) (cls : β → κ)
    (hcls : ∀ b b', cls b = cls b' → ∀ a, r a b ↔ r a b') (Δ s D : ℕ) (S : Finset β)
    (hS : Fintype.card α + S.card = Fintype.card β)
    (hclass : ∀ k, (S.filter fun b => cls b = k).card < (univ.filter fun b => cls b = k).card)
    (hdegα : ∀ a, degL r a ≤ Δ) (hdegβ : ∀ b, degR r b ≤ Δ)
    (hsα : ∀ a, Δ - degL (restrictR r S) a ≤ s)
    (hsβ : ∀ b : {b // b ∉ (S : Set β)}, Δ - degR (restrictR r (S : Set β)) b ≤ s)
    (hbig : 2 * s * (Δ + s + 1) < ∑ a, (Δ - degL (restrictR r (S : Set β)) a))
    (hD : (biGraph r).ediam ≤ D) :
    ∃ G : SimpleGraph (Fin (2 * Fintype.card α)), IsBipartiteRegDiam G Δ D :=
  regular_of_twins r Δ s D S hS (htwin_of_classes r cls hcls S hclass) hdegα hdegβ hsα hsβ hbig hD

end BipartiteDD.Regular
