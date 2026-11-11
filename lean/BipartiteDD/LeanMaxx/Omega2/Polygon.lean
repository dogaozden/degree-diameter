import BipartiteDD.LeanMaxx.Omega2.Main
import BipartiteDD.Hexagon.Main

/-!
# Theorem 2 for generalized hexagons

* `HexData.of_polygon`: a generalized hexagon (`GenPolygonGraph B 6`) with all degrees `q + 1` and a
  proper 2-colouring is a `HexData`.
* `omega2_ediam_polygon`: Theorem 2 for such a `B`.
* `omega2_ediam_inc`: the same for the incidence graph of points `P` and lines `L` (`Hexagon.incGraph inc`),
  with the partner map `point t ↦ line σ t`, `line l ↦ point σ⁻¹ l` for a bijection `σ : P ≃ L`.
-/

set_option linter.unusedSectionVars false

namespace BipartiteDD.LeanMaxx.Omega2

open SimpleGraph BipartiteDD.Doubling

theorem HexData.of_polygon {β : Type*} [Fintype β] {B : SimpleGraph β} [DecidableRel B.Adj] {q : ℕ}
    {κ : β → ZMod 2} (hB : GenPolygonGraph B 6) (hdeg : ∀ v, B.degree v = q + 1)
    (hκ : ∀ u v, B.Adj u v → κ u ≠ κ v) : HexData B q κ :=
  ⟨hB.egirth, reachable_of_ediam hB.ediam, hdeg, hκ⟩

variable {β V ι : Type*}

/-- **Theorem 2** for the incidence graph of a generalized hexagon of order `(q, q)`, `q ≥ 7`. -/
theorem omega2_ediam_polygon [Fintype β] [DecidableEq β] {B : SimpleGraph β} [DecidableRel B.Adj]
    {q : ℕ} {κ : β → ZMod 2} (hB : GenPolygonGraph B 6) (hdeg : ∀ v, B.degree v = q + 1)
    (hκ : ∀ u v, B.Adj u v → κ u ≠ κ v) (hq : 7 ≤ q) {π : β → β} (hπ : ∀ a, π (π a) = a)
    (hκπ : ∀ a, κ (π a) = κ a + 1)
    {G : SimpleGraph V} {f : V → β} {c : V → Option ι} {K : V → ZMod 2}
    (hK : ∀ u v, G.Adj u v → K u ≠ K v)
    (h1 : ∀ u w i j, G.Adj u w → c u = some i → c w = some j → i = j ∧ B.Adj (f u) (f w))
    (h2 : ∀ x w, G.Adj x w → c x = none → c w ≠ none ∧ (f w = f x ∨ f w = π (f x)))
    (hsurj : ∀ j s, ∃ v, c v = some j ∧ f v = s)
    (hconn : ∀ j u v, c u = some j → c v = some j →
      ∃ p : G.Walk u v, ∀ z ∈ p.support, c z ≠ none)
    {x : V} (hx : c x = none) {j : ι} (hmiss : ∀ w, G.Adj x w → c w ≠ some j) :
    (9 : ℕ∞) ≤ G.ediam :=
  omega2_ediam (HexData.of_polygon hB hdeg hκ) hq hπ hκπ hK h1 h2 hsurj hconn hx hmiss

section Inc

variable {P L : Type*} {inc : P → L → Prop}

/-- Point/line indicator. -/
def klass : P ⊕ L → ZMod 2 := Sum.elim (fun _ => 0) (fun _ => 1)

/-- The partner map: point `t ↦` line `σ t`, line `l ↦` point `σ⁻¹ l`. -/
def partner (σ : P ≃ L) : P ⊕ L → P ⊕ L := Sum.elim (fun p => Sum.inr (σ p)) (fun l => Sum.inl (σ.symm l))

theorem partner_partner (σ : P ≃ L) (a : P ⊕ L) : partner σ (partner σ a) = a := by
  rcases a with p | l <;> simp [partner]

theorem klass_partner (σ : P ≃ L) (a : P ⊕ L) : klass (partner σ a) = klass a + 1 := by
  rcases a with p | l
  · simp [partner, klass]
  · simp only [partner, klass, Sum.elim_inr, Sum.elim_inl]; decide

theorem klass_proper (u v : P ⊕ L) (h : (Hexagon.incGraph inc).Adj u v) : klass u ≠ klass v := by
  rcases u with p | l <;> rcases v with p' | l' <;> simp_all [klass, Hexagon.incGraph]

theorem degree_inl [Fintype P] [Fintype L] [DecidableRel (Hexagon.incGraph inc).Adj] (p : P) :
    (Hexagon.incGraph inc).degree (Sum.inl p) = Nat.card {l // inc p l} := by
  rw [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr (Equiv.symm
    { toFun := fun l => ⟨Sum.inr l.1, l.2⟩
      invFun := fun x => by
        rcases x with ⟨_ | l, h⟩
        · exact (False.elim h)
        · exact ⟨l, h⟩
      left_inv := fun l => rfl
      right_inv := fun x => by rcases x with ⟨_ | l, h⟩ <;> first | exact (False.elim h) | rfl })

theorem degree_inr [Fintype P] [Fintype L] [DecidableRel (Hexagon.incGraph inc).Adj] (l : L) :
    (Hexagon.incGraph inc).degree (Sum.inr l) = Nat.card {p // inc p l} := by
  rw [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr (Equiv.symm
    { toFun := fun p => ⟨Sum.inl p.1, p.2⟩
      invFun := fun x => by
        rcases x with ⟨p | _, h⟩
        · exact ⟨p, h⟩
        · exact (False.elim h)
      left_inv := fun p => rfl
      right_inv := fun x => by rcases x with ⟨p | _, h⟩ <;> first | exact (False.elim h) | rfl })

/-- **Theorem 2**, incidence-structure form (the statement of the note): `B` is the incidence graph of a
generalized hexagon of order `(q, q)`, `q ≥ 7`, `σ` a bijection from points to lines, and every new vertex
`x` (label `f x`) is adjacent only to copy vertices labelled by its own point `t` or its line `σ t`
(or, for `f x = line l`, by `l` or the point `σ⁻¹ l`). Then `G` has a pair of vertices at distance `≥ 9`. -/
theorem omega2_ediam_inc [Fintype P] [Fintype L] [DecidableRel (Hexagon.incGraph inc).Adj]
    (hB : GenPolygonGraph (Hexagon.incGraph inc) 6) {q : ℕ} (hq : 7 ≤ q)
    (hP : ∀ p, Nat.card {l // inc p l} = q + 1) (hL : ∀ l, Nat.card {p // inc p l} = q + 1)
    (σ : P ≃ L)
    {G : SimpleGraph V} {f : V → P ⊕ L} {c : V → Option ι} {K : V → ZMod 2}
    (hK : ∀ u v, G.Adj u v → K u ≠ K v)
    (h1 : ∀ u w i j, G.Adj u w → c u = some i → c w = some j →
      i = j ∧ (Hexagon.incGraph inc).Adj (f u) (f w))
    (h2 : ∀ x w, G.Adj x w → c x = none →
      c w ≠ none ∧ (f w = f x ∨ f w = partner σ (f x)))
    (hsurj : ∀ j s, ∃ v, c v = some j ∧ f v = s)
    (hconn : ∀ j u v, c u = some j → c v = some j →
      ∃ p : G.Walk u v, ∀ z ∈ p.support, c z ≠ none)
    {x : V} (hx : c x = none) {j : ι} (hmiss : ∀ w, G.Adj x w → c w ≠ some j) :
    (9 : ℕ∞) ≤ G.ediam := by
  classical
  refine omega2_ediam_polygon (κ := klass) hB ?_ klass_proper hq (partner_partner σ)
    (klass_partner σ) hK h1 h2 hsurj hconn hx hmiss
  intro v
  rcases v with p | l
  · rw [degree_inl, hP]
  · rw [degree_inr, hL]

end Inc

end BipartiteDD.LeanMaxx.Omega2
