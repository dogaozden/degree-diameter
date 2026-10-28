import BipartiteDD.Haar.Graph
import BipartiteDD.LeanMaxx.Haarbound.Sphere
import BipartiteDD.LeanMaxx.Haarbound.Arith
import Mathlib.Combinatorics.SimpleGraph.Diam

/-! Theorem 4.1 of `research/theorems/HAAR_D8_10.md` (the per-side Moore bound for Haar graphs).

Statement: for a finite group `G` and `S : Finset G` with `S.card = Δ ≥ 2`, if the Haar graph
`H(G, S)` has `ediam ≤ D`, then `|G| ≤ ∑_{j < D} (Δ - 1)^j`.

Proof (as in the note). Every vertex `(x, B)` of the far side lies at distance `≤ D - 1` from the
base vertex `(e, A)`, at a distance of the right parity. The layers `S_L((e,A))` for these `L` have
at most `Δ (Δ - 1)^(L-1)` vertices (`Sphere.lean`, valid since the graph has degree `≤ Δ`), and the
sum of those bounds is `∑_{j < D} (Δ - 1)^j` (`Arith.lean`). When `D` is odd the far side is the `A`
side, with the identity layer `L = 0` included, which is the same count. -/

namespace BipartiteDD.LeanMaxx.HaarBound

open Finset SimpleGraph BipartiteDD.Haar

variable {G : Type*} [Group G]

/-- Every vertex of `H(G, S)` has at most `|S|` neighbours. -/
theorem neighborFinset_card_le [Fintype G] [DecidableEq G] (S : Finset G) [DecidableRel (haarGraph S).Adj]
    (w : G ⊕ G) : ((haarGraph S).neighborFinset w).card ≤ S.card := by
  cases w with
  | inl g =>
    have hsub : (haarGraph S).neighborFinset (Sum.inl g) ⊆ S.image (fun s => Sum.inr (s * g)) := by
      intro x hx
      rw [mem_neighborFinset] at hx
      cases x with
      | inl h => exact absurd hx (haarGraph_not_adj_inl_inl S g h)
      | inr h =>
        rw [haarGraph_adj_inl_inr] at hx
        rw [mem_image]
        exact ⟨h * g⁻¹, hx, by simp⟩
    exact (card_le_card hsub).trans card_image_le
  | inr h =>
    have hsub : (haarGraph S).neighborFinset (Sum.inr h) ⊆ S.image (fun s => Sum.inl (s⁻¹ * h)) := by
      intro x hx
      rw [mem_neighborFinset] at hx
      cases x with
      | inl g =>
        rw [haarGraph_adj_inr_inl] at hx
        rw [mem_image]
        exact ⟨h * g⁻¹, hx, by simp⟩
      | inr h' => exact absurd hx (haarGraph_not_adj_inr_inr S h h')
    exact (card_le_card hsub).trans card_image_le

/-- Adjacent vertices of `H(G, S)` lie on opposite sides. -/
theorem isLeft_ne_of_adj {S : Finset G} {v w : G ⊕ G} (h : (haarGraph S).Adj v w) :
    v.isLeft ≠ w.isLeft := by
  rcases v with g | g <;> rcases w with g' | g'
  · exact absurd h (haarGraph_not_adj_inl_inl S g g')
  · simp
  · simp
  · exact absurd h (haarGraph_not_adj_inr_inr S g g')

/-- A walk has even length exactly when its ends lie on the same side. -/
theorem even_length_iff_isLeft {S : Finset G} {u w : G ⊕ G} (p : (haarGraph S).Walk u w) :
    Even p.length ↔ u.isLeft = w.isLeft := by
  have key : ∀ a b c : Bool, a ≠ b → (¬(b = c) ↔ a = c) := by decide
  induction p with
  | nil => simp
  | cons h p ih =>
    rw [SimpleGraph.Walk.length_cons, Nat.even_add_one]
    exact (not_congr ih).trans (key _ _ _ (isLeft_ne_of_adj h))

/-- **Theorem 4.1 (Haar per-side Moore bound).** If `S.card = Δ ≥ 2` and `H(G, S)` has diameter at
most `D`, then `|G| ≤ ∑_{j < D} (Δ - 1)^j`. -/
theorem card_le [Fintype G] {Δ D : ℕ} (S : Finset G) (hS : S.card = Δ)
    (hΔ : 2 ≤ Δ) (hdiam : (haarGraph S).ediam ≤ D) :
    Fintype.card G ≤ ∑ j ∈ Finset.range D, (Δ - 1) ^ j := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, Δ = k + 1 := ⟨Δ - 1, by omega⟩
  rw [Nat.add_sub_cancel, ← parSum_eq k D]
  have hdeg : ∀ u, ((haarGraph S).neighborFinset u).card ≤ k + 1 := fun u => by
    have := neighborFinset_card_le S u
    omega
  -- the far side: `(x, A)` for `D` odd, `(x, B)` for `D` even
  let ι : G → G ⊕ G := fun x => if D % 2 = 1 then Sum.inl x else Sum.inr x
  have hι : Function.Injective ι := by
    intro x y hxy
    simp only [ι] at hxy
    split_ifs at hxy <;> simpa using hxy
  have hιleft : ∀ x, (ι x).isLeft = true ↔ D % 2 = 1 := by
    intro x
    by_cases hD : D % 2 = 1 <;> simp [ι, hD]
  -- every far-side vertex lies in a layer `L < D` with `L ≡ D - 1 (mod 2)`
  have hcover : ∀ x, ∃ m ∈ (range D).filter (fun L => L % 2 = (D + 1) % 2),
      ι x ∈ sphere (haarGraph S) (Sum.inl 1) m := by
    intro x
    have hle : (haarGraph S).edist (Sum.inl 1) (ι x) ≤ (D : ℕ∞) :=
      le_trans edist_le_ediam hdiam
    have hfin : (haarGraph S).edist (Sum.inl 1) (ι x) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENat.natCast_ne_top D) hle
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
    rw [← hm] at hle
    have hmD : m ≤ D := by exact_mod_cast hle
    obtain ⟨p, hp⟩ := exists_walk_of_edist_eq_coe hm.symm
    have hpar := even_length_iff_isLeft p
    rw [hp] at hpar
    have hL : (Sum.inl (1 : G) : G ⊕ G).isLeft = true := rfl
    have hpar' : Even m ↔ D % 2 = 1 := by
      rw [hpar, ← hιleft x, hL]
      exact eq_comm
    rw [Nat.even_iff] at hpar'
    have hmD' : m < D ∧ m % 2 = (D + 1) % 2 := by
      rcases Nat.mod_two_eq_zero_or_one D with hD | hD
      · simp [hD] at hpar'
        omega
      · simp [hD] at hpar'
        omega
    exact ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hmD'.1, hmD'.2⟩, mem_sphere.mpr hm.symm⟩
  -- each layer has at most `bnd k L` vertices
  have hlayer : ∀ L, (sphere (haarGraph S) (Sum.inl 1) L).card ≤ bnd k L := by
    intro L
    cases L with
    | zero => simpa [bnd] using card_sphere_zero (haarGraph S) (Sum.inl 1)
    | succ m =>
      have := card_sphere_le (haarGraph S) (k + 1) hdeg (Sum.inl 1) m
      simpa [bnd] using this
  calc Fintype.card G = (univ.image ι).card := by
        rw [card_image_of_injective _ hι, card_univ]
    _ ≤ (((range D).filter (fun L => L % 2 = (D + 1) % 2)).biUnion
          fun L => sphere (haarGraph S) (Sum.inl 1) L).card := by
        apply card_le_card
        intro w hw
        obtain ⟨x, -, rfl⟩ := mem_image.mp hw
        obtain ⟨m, hm, hmem⟩ := hcover x
        exact mem_biUnion.mpr ⟨m, hm, hmem⟩
    _ ≤ ∑ L ∈ (range D).filter (fun L => L % 2 = (D + 1) % 2),
          (sphere (haarGraph S) (Sum.inl 1) L).card := card_biUnion_le
    _ ≤ ∑ L ∈ (range D).filter (fun L => L % 2 = (D + 1) % 2), bnd k L :=
        Finset.sum_le_sum fun L _ => hlayer L
    _ = parSum k D := rfl

end BipartiteDD.LeanMaxx.HaarBound
