import BipartiteDD.LeanMaxx.Omega3.Balls
import BipartiteDD.LeanMaxx.Omega3.Tables
import BipartiteDD.LeanMaxx.Omega3.Shape

/-!
# Theorem 3.3 (normal form)

`B` is the incidence graph of a generalized hexagon of order `(q, q)`, `q ≥ 8`, in the sense of `Hex`;
`α` blocks of five copies, `2 α ≤ q + 3`, each of type a or b (`typ`); `ε₀` is the colour of the unbarred
hubs (`0`: reading 2, unbarred hubs on points; `1`: its point/line dual); `lam c` is a colour-preserving
automorphism of `B` for every copy `c` (a *twisted* labelling in the normal form of Lemma 1.1).

`omega3_ediam`: the graph `ΩH_q` has diameter at least `9`.

Proof: fix a row `t` of colour `ε₀` and the unbarred hub `(0, t)`; take the missed copy `c'` of Lemma 3.2.
By `walk_route` and `shape`, every vertex of `c'` within distance `7` of the hub lies in a ball of `CovP`;
by `Balls` these balls contain fewer than `q⁵` of the `≥ q⁵` vertices opposite `t`. An opposite vertex
`y'` outside the balls is at odd distance `> 7`, hence `≥ 9`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace BipartiteDD.LeanMaxx.Omega3

open Finset BipartiteDD.LeanMaxx.Omega2

variable {β : Type*} [Fintype β] [DecidableEq β] {B : SimpleGraph β} [DecidableRel B.Adj]
  {κ : β → ZMod 2} {q α : ℕ}

/-- The union of the balls of Theorem 3.3 that cover the vertices of `c'` near the hub. -/
noncomputable def covSet (B : SimpleGraph β) (typ : Fin α → Bool) (lam : Copy α → Equiv.Perm β) (t : β)
    (c' : Copy α) : Finset β :=
  (F0 typ 0 c').biUnion (fun c₁ => ballOpp B t (cen lam t c₁ c') 4) ∪
  (F1 typ 0 c').biUnion (fun x => ballOpp B t (cen lam t x c') 2) ∪
  (F2 typ 0 c').biUnion (fun p => ballOpp B t (cen lam t p.1 p.2) 2) ∪
  (F3 typ 0 c' \ F0 typ 0 c').biUnion (fun c₁ => ballOpp B t (cen lam t c₁ c') 2)

theorem mem_covSet {typ : Fin α → Bool} {lam : Copy α → Equiv.Perm β} {t y' : β} {c' : Copy α}
    (h6 : B.dist t y' = 6) (h : CovP typ B lam t y' c') : y' ∈ covSet B typ lam t c' := by
  unfold covSet
  simp only [Finset.mem_union, Finset.mem_biUnion, mem_ballOpp]
  rcases h with ⟨c₁, h1, h2⟩ | ⟨x, h1, h2⟩ | ⟨p, h1, h2⟩ | ⟨c₁, h1, h2⟩
  · exact Or.inl (Or.inl (Or.inl ⟨c₁, h1, h6, h2⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨x, h1, h6, h2⟩))
  · exact Or.inl (Or.inr ⟨p, h1, h6, h2⟩)
  · exact Or.inr ⟨c₁, h1, h6, h2⟩

theorem card_biUnion_ball {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → β) (t : β) (r bound : ℕ)
    (h : ∀ i ∈ s, (ballOpp B t (f i) r).card ≤ bound) :
    (s.biUnion fun i => ballOpp B t (f i) r).card ≤ s.card * bound :=
  Finset.card_biUnion_le.trans (Finset.sum_le_card_nsmul _ _ _ h)

theorem col_cen (lam : Copy α → autSub B κ) (t : β) (c d : Copy α) :
    κ (cen (fun c => (lam c : Equiv.Perm β)) t c d) = κ t := by
  have h1 := (lam d).2.2 ((lam c : Equiv.Perm β)⁻¹ t)
  have h2 := ((lam c)⁻¹).2.2 t
  simp only [cen, Equiv.Perm.mul_apply]
  rw [h1]
  simpa using h2

theorem card_covSet_le (H : Hex B κ q) (hq : 1 ≤ q) (typ : Fin α → Bool) (lam : Copy α → autSub B κ)
    (t : β) (c' : Copy α) :
    (covSet B typ (fun c => (lam c : Equiv.Perm β)) t c').card ≤
      (F0 typ 0 c').card * (q ^ 4 + 2 * q ^ 2) + m2 typ 0 c' * q ^ 2 := by
  have hc := col_cen lam t
  have b4 : ∀ c d : Copy α, (ballOpp B t (cen (fun c => (lam c : Equiv.Perm β)) t c d) 4).card ≤ q ^ 4 + 2 * q ^ 2 :=
    fun c d => card_ballOpp_four_le H hq (hc c d)
  have b2 : ∀ c d : Copy α, (ballOpp B t (cen (fun c => (lam c : Equiv.Perm β)) t c d) 2).card ≤ q ^ 2 :=
    fun c d => card_ballOpp_two_le H hq (hc c d)
  unfold covSet m2
  have e0 := card_biUnion_ball (F0 typ 0 c') (fun c₁ => cen (fun c => (lam c : Equiv.Perm β)) t c₁ c') t 4
    (q ^ 4 + 2 * q ^ 2) (fun i _ => b4 _ _)
  have e1 := card_biUnion_ball (F1 typ 0 c') (fun x => cen (fun c => (lam c : Equiv.Perm β)) t x c') t 2
    (q ^ 2) (fun i _ => b2 _ _)
  have e2 := card_biUnion_ball (F2 typ 0 c') (fun p => cen (fun c => (lam c : Equiv.Perm β)) t p.1 p.2) t 2
    (q ^ 2) (fun i _ => b2 _ _)
  have e3 := card_biUnion_ball (F3 typ 0 c' \ F0 typ 0 c')
    (fun c₁ => cen (fun c => (lam c : Equiv.Perm β)) t c₁ c') t 2 (q ^ 2) (fun i _ => b2 _ _)
  have u1 := Finset.card_union_le ((F0 typ 0 c').biUnion fun c₁ => ballOpp B t (cen (fun c => (lam c : Equiv.Perm β)) t c₁ c') 4)
    ((F1 typ 0 c').biUnion fun x => ballOpp B t (cen (fun c => (lam c : Equiv.Perm β)) t x c') 2)
  have u2 := Finset.card_union_le (((F0 typ 0 c').biUnion fun c₁ => ballOpp B t (cen (fun c => (lam c : Equiv.Perm β)) t c₁ c') 4) ∪
    ((F1 typ 0 c').biUnion fun x => ballOpp B t (cen (fun c => (lam c : Equiv.Perm β)) t x c') 2))
    ((F2 typ 0 c').biUnion fun p => ballOpp B t (cen (fun c => (lam c : Equiv.Perm β)) t p.1 p.2) 2)
  have u3 := Finset.card_union_le ((((F0 typ 0 c').biUnion fun c₁ => ballOpp B t (cen (fun c => (lam c : Equiv.Perm β)) t c₁ c') 4) ∪
    ((F1 typ 0 c').biUnion fun x => ballOpp B t (cen (fun c => (lam c : Equiv.Perm β)) t x c') 2)) ∪
    ((F2 typ 0 c').biUnion fun p => ballOpp B t (cen (fun c => (lam c : Equiv.Perm β)) t p.1 p.2) 2))
    ((F3 typ 0 c' \ F0 typ 0 c').biUnion fun c₁ => ballOpp B t (cen (fun c => (lam c : Equiv.Perm β)) t c₁ c') 2)
  nlinarith


theorem zmod2_aux (e x : ZMod 2) (h : e = e + 1 + x) : x = 1 := by
  revert h; revert e x; decide

theorem zmod2_eq_of_ne_of_ne {a b c : ZMod 2} (h1 : a ≠ b) (h2 : a ≠ c) : b = c := by
  revert h1 h2; revert a b c; decide

/-- Some row of colour `ε₀` exists. -/
theorem exists_row [Nonempty β] (H : Hex B κ q) (ε₀ : ZMod 2) : ∃ t, κ t = ε₀ := by
  obtain ⟨v⟩ := ‹Nonempty β›
  by_cases h : κ v = ε₀
  · exact ⟨v, h⟩
  · have hpos : 0 < B.degree v := by rw [H.deg]; omega
    obtain ⟨w, hw⟩ := (SimpleGraph.degree_pos_iff_exists_adj B v).1 hpos
    exact ⟨w, zmod2_eq_of_ne_of_ne (H.col v w hw) h⟩

/-- The marks of the normal form are colour-preserving automorphisms. -/
theorem nfmk_mem (lam : Copy α → autSub B κ) (bar : Bool) (c : Copy α) :
    nfmk (fun c => (lam c : Equiv.Perm β)) bar c ∈ autSub B κ := by
  cases bar
  · exact (autSub B κ).one_mem
  · exact (lam c).2

theorem nfmk_col (lam : Copy α → autSub B κ) (bar : Bool) (c : Copy α) (u : β) :
    κ (nfmk (fun c => (lam c : Equiv.Perm β)) bar c u) = κ u := (nfmk_mem lam bar c).2 u

/-- **Theorem 3.3 (normal form), far pair.** For `q ≥ 8`, every block pattern and every twisted labelling
`lam : Copy α → Aut(B)`, `ΩH_q` has two vertices (a hub and a vertex of a copy it misses) at distance
at least `9`. -/
theorem omega3_far [Nonempty β] (H : Hex B κ q) (hq : 8 ≤ q) {α : ℕ} (hα : 0 < α) (h2 : 2 * α ≤ q + 3)
    (typ : Fin α → Bool) (ε₀ : ZMod 2) (lam : Copy α → autSub B κ) :
    ∃ x y, (9 : ℕ∞) ≤ (omega B κ typ ε₀ (nfmk (fun c => (lam c : Equiv.Perm β)))).edist x y := by
  set mk := nfmk (fun c => (lam c : Equiv.Perm β)) with hmk
  obtain ⟨t, ht⟩ := exists_row H ε₀
  obtain ⟨hc'not, hnum⟩ := star_exists typ hα hq h2
  set c' := cstar typ hα with hc'
  -- an opposite vertex outside the covering balls
  have hcard : (covSet B typ (fun c => (lam c : Equiv.Perm β)) t c').card < (opp B t).card := by
    have h1 := card_covSet_le H (by omega) typ lam t c'
    have h2' := q_pow_five_le_card_sph_six H.col H.deg H.girth H.reach (u := t) (show 1 ≤ q by omega)
    exact lt_of_le_of_lt h1 (lt_of_lt_of_le hnum h2')
  obtain ⟨y', hy'opp, hy'not⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hy6 : B.dist t y' = 6 := mem_opp.1 hy'opp
  -- the hub and the far copy vertex
  set h : Hub κ ε₀ := ⟨false, 0, t, by simpa using ht⟩ with hh
  have key : ∀ W : (omega B κ typ ε₀ mk).Walk (Sum.inr h) (Sum.inl (c', y')), 9 ≤ W.length := by
    intro W
    by_contra hlt
    have hlt' : W.length < 9 := Nat.lt_of_not_le hlt
    -- parity
    have hpar := col_walk (fun a b hab => Kcol_proper H.col (nfmk_col lam) hab) W
    have hKv : Kcol (α := α) (κ := κ) (ε₀ := ε₀) (Sum.inl (c', y')) = ε₀ := by
      simp only [Kcol, Sum.elim_inl]
      rw [← col_opp H hy6, ht]
    have hKh : Kcol (α := α) (κ := κ) (ε₀ := ε₀) (Sum.inr h) = ε₀ + 1 := by
      simp only [Kcol, Sum.elim_inr, hh]; rw [ht]
    rw [hKv, hKh] at hpar
    have hodd : (W.length : ZMod 2) = 1 := zmod2_aux ε₀ _ hpar
    obtain ⟨m, hm⟩ := (ZMod.natCast_eq_one_iff_odd.1 hodd)
    have hle : W.length ≤ 7 := by omega
    cases W with
    | @cons _ x _ hadj W' =>
      rcases x with ⟨c₁, y₁⟩ | h₂
      · rw [omega_adj_hc] at hadj
        obtain ⟨hmeet, hy₁⟩ := hadj
        have hy₁t : y₁ = t := by rw [hy₁]; simp [hmk, nfmk, hh]
        subst hy₁t
        have hlen : W'.length ≤ 6 := by simp at hle; omega
        obtain ⟨fn, a, hr, ha, wB, hwB⟩ :=
          walk_route H.col (nfmk_col lam) (nfmk_mem lam) _ c₁ _ c' y' W' rfl
        have hshape := shape (typ := typ) (lam := fun c => (lam c : Equiv.Perm β)) (ε₀ := ε₀)
          ((mem_CuK typ).2 hmeet) hc'not (by rwa [ht] at hr) (by omega) ⟨wB, hwB⟩ (by omega)
        exact hy'not (mem_covSet hy6 hshape)
      · exact absurd hadj not_omega_adj_hh
  have hedist : (9 : ℕ∞) ≤ (omega B κ typ ε₀ mk).edist (Sum.inr h) (Sum.inl (c', y')) := by
    unfold SimpleGraph.edist
    refine le_iInf fun W => ?_
    exact_mod_cast key W
  exact ⟨_, _, hedist⟩

/-- **Theorem 3.3 (normal form).** For `q ≥ 8`, every block pattern and every twisted labelling
`lam : Copy α → Aut(B)`, `ΩH_q` has diameter at least `9`. -/
theorem omega3_ediam [Nonempty β] (H : Hex B κ q) (hq : 8 ≤ q) {α : ℕ} (hα : 0 < α) (h2 : 2 * α ≤ q + 3)
    (typ : Fin α → Bool) (ε₀ : ZMod 2) (lam : Copy α → autSub B κ) :
    (9 : ℕ∞) ≤ (omega B κ typ ε₀ (nfmk (fun c => (lam c : Equiv.Perm β)))).ediam := by
  obtain ⟨x, y, h⟩ := omega3_far H hq hα h2 typ ε₀ lam
  exact h.trans SimpleGraph.edist_le_ediam

end BipartiteDD.LeanMaxx.Omega3
