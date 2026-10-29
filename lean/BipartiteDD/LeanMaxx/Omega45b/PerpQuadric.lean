import BipartiteDD.LeanMaxx.Omega45b.Main

/-!
# Lemma 4.4 for `H(7)`, stated in terms of the quadric

`Lemma44` says: every collineation `h` of `H(7)` (an automorphism of the incidence graph `G7` preserving
the colours) that fixes no point moves at most `4144` points `s` to a point `h s` with `Bf s (h s) = 0` (that is,
`h s` at distance `≤ 4` from `s`, by `dist_inl_le_four_iff`). `perpBound_of_lemma44` turns it into the abstract
statement `PerpBound` used by `Omega45/Q7.lean`. This is the only statement still missing for Theorem 4.5
(`omega45_H7_geometric`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace BipartiteDD.LeanMaxx.Omega45b

open BipartiteDD.Hexagon BipartiteDD.LeanMaxx.Omega2 BipartiteDD.LeanMaxx.Omega3 BipartiteDD.LeanMaxx.Omega45

/-- **Lemma 4.4 for `H(7)`** (the note proves it by a character sum, for `q = 7`, `|Perp(h)| ≤ 4144`). -/
def Lemma44 : Prop :=
  ∀ h : autSub G7 klass, (∀ p : SPt F7, (h : Equiv.Perm (SPt F7 ⊕ HLine F7)) (Sum.inl p) ≠ Sum.inl p) →
    Nat.card {s : SPt F7 // ∃ p : SPt F7, (h : Equiv.Perm (SPt F7 ⊕ HLine F7)) (Sum.inl s) = Sum.inl p ∧
      Bf s.1.rep p.1.rep = 0} ≤ 4144

open scoped Classical in
theorem perpBound_of_lemma44 [Fintype (SPt F7 ⊕ HLine F7)] [DecidableEq (SPt F7 ⊕ HLine F7)]
    [DecidableRel G7.Adj] (hL : Lemma44) : PerpBound G7 klass 0 4144 := by
  intro h hfix
  refine le_trans ?_ (hL h (fun p => hfix _ rfl))
  let S : Finset (SPt F7) := Finset.univ.filter fun s => ∃ p : SPt F7,
    (h : Equiv.Perm (SPt F7 ⊕ HLine F7)) (Sum.inl s) = Sum.inl p ∧ Bf s.1.rep p.1.rep = 0
  have hS : PerpSet G7 klass 0 (h : Equiv.Perm (SPt F7 ⊕ HLine F7)) =
      S.map ⟨Sum.inl, Sum.inl_injective⟩ := by
    ext v
    simp only [PerpSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk, S]
    constructor
    · rintro ⟨hk, hd⟩
      rcases v with s | l
      · have hk' : klass ((h : Equiv.Perm (SPt F7 ⊕ HLine F7)) (Sum.inl s)) = 0 := by
          rw [h.2.2]; simp [klass]
        rcases hv : (h : Equiv.Perm (SPt F7 ⊕ HLine F7)) (Sum.inl s) with p | l'
        · rw [hv] at hd
          exact ⟨s, ⟨p, hv, (dist_inl_le_four_iff s p).1 hd⟩, rfl⟩
        · rw [hv] at hk'; simp [klass] at hk'
      · simp [klass] at hk
    · rintro ⟨s, ⟨p, hp, hb⟩, rfl⟩
      refine ⟨by simp [klass], ?_⟩
      rw [hp]
      exact (dist_inl_le_four_iff s p).2 hb
  rw [hS, Finset.card_map, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- **Theorem 4.5 at `H(7)`, modulo Lemma 4.4 (`Lemma44`) only.** `ΩH₇` has diameter `≥ 9` for every geometric
labelling, in reading 2 (`ε₀ = 0`) and in its dual (`ε₀ = 1`), every block pattern with `α ≥ 1` blocks
(`2 α ≤ 10`; Gómez's wiring has `α = 5`). -/
theorem omega45_H7_geometric (hL : Lemma44) {α : ℕ} (hα : 0 < α) (h2 : 2 * α ≤ 7 + 3)
    (typ : Fin α → Bool) (ε₀ : ZMod 2) (μ : Copy α → Equiv.Perm (SPt F7 ⊕ HLine F7))
    (hμ : ∀ c u, klass (μ c u) = klass u) (hgeo : Geometric G7 klass μ) :
    (9 : ℕ∞) ≤ (omega G7 klass typ ε₀ (labMk μ)).ediam := by
  obtain ⟨_, _, _, H⟩ := hex_hexagon (F := F7)
  haveI := nonempty_hexagon (F := F7)
  rw [ZMod.card] at H
  refine omega45_H7_of_perpBound H hα h2 typ ε₀ ?_ μ hμ hgeo (perpBound_of_lemma44 hL)
  revert ε₀
  decide

end BipartiteDD.LeanMaxx.Omega45b
