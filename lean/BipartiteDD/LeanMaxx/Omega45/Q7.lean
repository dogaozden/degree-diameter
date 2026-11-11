import BipartiteDD.LeanMaxx.Omega45.Tab7

/-!
# `q = 7`: Lemma 4.2, and Theorem 4.5 from Lemmas 4.3 and 4.4

`B` is the incidence graph of a generalized hexagon of order `(7, 7)` (`Hex B κ 7`), `ε₀` the colour of
the unbarred hubs, `typ : Fin α → Bool` the block types (`2 α ≤ 10`), `lam c` the twist of copy `c` (normal
form of Lemma 1.1), `c' = cstar typ hα` the missed copy of Lemma 3.2.

* `omega45_lemma42` (**Lemma 4.2**, unconditional): if at some row `t` of colour `ε₀` two of
  `t, y₁(t), …, y₅(t)` coincide, then `ΩH₇` has a far pair. `y_c(t) = λ_{c'} λ_c⁻¹ (t)`, `c ∈ F0`.
* `omega45_of_hyps` (**Theorem 4.5 as a reduction**): if the hexagon satisfies the two statements that the note
  proves by computer (`Bonferroni`, Lemma 4.3) and by a character-sum bound (`PerpBound`, Lemma 4.4), then
  `ΩH₇` has a far pair, hence diameter `≥ 9`. The final double count of the note is proved in full.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace BipartiteDD.LeanMaxx.Omega45

open Finset BipartiteDD.LeanMaxx.Omega2 BipartiteDD.LeanMaxx.Omega3

variable {β : Type*} [Fintype β] [DecidableEq β] {B : SimpleGraph β} [DecidableRel B.Adj]
  {κ : β → ZMod 2} {q α : ℕ}

/-- Automorphisms preserve the distance. -/
theorem dist_le_aut (H : Hex B κ q) (g : autSub B κ) (u v : β) :
    B.dist ((g : Equiv.Perm β) u) ((g : Equiv.Perm β) v) ≤ B.dist u v := by
  obtain ⟨p, hp⟩ := (H.reach u v).exists_walk_length_eq_dist
  let φ : B →g B := ⟨(g : Equiv.Perm β), fun {a b} h => (g.2.1 a b).2 h⟩
  have h := SimpleGraph.dist_le (p.map φ)
  rw [SimpleGraph.Walk.length_map] at h
  exact h.trans (le_of_eq hp)

theorem dist_aut (H : Hex B κ q) (g : autSub B κ) (u v : β) :
    B.dist ((g : Equiv.Perm β) u) ((g : Equiv.Perm β) v) = B.dist u v := by
  refine le_antisymm (dist_le_aut H g u v) ?_
  have := dist_le_aut H g⁻¹ ((g : Equiv.Perm β) u) ((g : Equiv.Perm β) v)
  simpa using this

/-- **Lemma 4.2** (`q = 7`). If, at a row `t` of colour `ε₀`, at most four of the radius-4 centres differ from
`t` (two of `t, y₁(t), …, y₅(t)` coincide), then `ΩH₇` has a pair of vertices at distance `≥ 9`: the hub
`(0, t)` and a vertex of the missed copy. -/
theorem omega45_lemma42 [Nonempty β] (H : Hex B κ 7) {α : ℕ} (hα : 0 < α) (h2 : 2 * α ≤ 7 + 3)
    (typ : Fin α → Bool) {ε₀ : ZMod 2} (lam : Copy α → autSub B κ) {t : β} (ht : κ t = ε₀)
    (hn : ((cen4 typ (fun c => (lam c : Equiv.Perm β)) t (cstar typ hα)).erase t).card ≤ 4) :
    ∃ x y, (9 : ℕ∞) ≤ (omega B κ typ ε₀ (nfmk (fun c => (lam c : Equiv.Perm β)))).edist x y :=
  far_of_centres H (by norm_num) lam ht (cstar_not_mem typ hα) hn (star7 typ hα h2).1 (by norm_num)


/-- **`q = 7`, at most four blocks (unconditional).** In every generalized hexagon of order `(7, 7)`, for
`α ≤ 4` blocks of five copies (so `10α ≤ 40` hubs rows of degree `2α ≤ 8 < q + 3`), every twisted labelling
gives a far pair. With `α ≤ 4` at most four radius-4 centres exist, so Lemma 4.2 applies at every row. (Gómez's
wiring has `α = 5`; this is not the table case.) -/
theorem omega45_alpha_le_four [Nonempty β] (H : Hex B κ 7) {α : ℕ} (hα : 0 < α) (hα4 : α ≤ 4)
    (typ : Fin α → Bool) (ε₀ : ZMod 2) (lam : Copy α → autSub B κ) :
    ∃ x y, (9 : ℕ∞) ≤ (omega B κ typ ε₀ (nfmk (fun c => (lam c : Equiv.Perm β)))).edist x y := by
  obtain ⟨t, ht⟩ := exists_row H ε₀
  refine omega45_lemma42 H hα (by omega) typ lam ht ?_
  have h1 : ((cen4 typ (fun c => (lam c : Equiv.Perm β)) t (cstar typ hα)).erase t).card ≤
      (cen4 typ (fun c => (lam c : Equiv.Perm β)) t (cstar typ hα)).card := Finset.card_erase_le
  have h2 : (cen4 typ (fun c => (lam c : Equiv.Perm β)) t (cstar typ hα)).card ≤
      (F0 typ 0 (cstar typ hα)).card := Finset.card_image_le
  have h3 := (star7 typ hα (by omega)).2
  omega

/-! ### Lemma 4.4 and Lemma 4.3 as statements about the hexagon -/

/-- The rows `s` of colour `ε₀` that `h` moves to a row at distance `≤ 4` (perpendicular or equal points when
`ε₀` is the colour of the points). -/
noncomputable def PerpSet (B : SimpleGraph β) (κ : β → ZMod 2) (ε₀ : ZMod 2) (h : Equiv.Perm β) : Finset β :=
  univ.filter fun s => κ s = ε₀ ∧ B.dist s (h s) ≤ 4

/-- **Lemma 4.4 (statement).** Every collineation without a fixed point among the rows of colour `ε₀` moves at
most `N` of them to a row at distance `≤ 4` (`N = 4144` for `H(7)` in the note). -/
def PerpBound (B : SimpleGraph β) (κ : β → ZMod 2) (ε₀ : ZMod 2) (N : ℕ) : Prop :=
  ∀ h : autSub B κ, (∀ s, κ s = ε₀ → (h : Equiv.Perm β) s ≠ s) → (PerpSet B κ ε₀ h).card ≤ N

/-- **Lemma 4.3 (statement).** Six distinct rows `t, y₁, …, y₅` of colour `ε₀` of which fewer than `k` of the
fifteen pairs are at distance `≤ 4` (the count `2 A + Bc` is twice the number of such pairs): the radius-4
balls around the `yᵢ` cover so few rows opposite `t` that `m` radius-2 balls (`≤ q²` rows each) cannot cover
the rest. The note proves this for `k = 6`, `m = 140`; the reduction below needs only `k = 4`
(`bonferroni_mono`). -/
def Bonferroni (B : SimpleGraph β) (κ : β → ZMod 2) (ε₀ : ZMod 2) (k m : ℕ) : Prop :=
  ∀ (t : β) (Y : Finset β), κ t = ε₀ → Y.card = 5 → (∀ y ∈ Y, κ y = ε₀ ∧ y ≠ t) →
    2 * (Y.filter fun y => B.dist t y ≤ 4).card +
      ((Y ×ˢ Y).filter fun p => p.1 ≠ p.2 ∧ B.dist p.1 p.2 ≤ 4).card < 2 * k →
    (Y.biUnion fun y => ballOpp B t y 4).card + m * 7 ^ 2 < 7 ^ 5

theorem bonferroni_mono {k k' m : ℕ} (h : k' ≤ k) (hB : Bonferroni B κ ε₀ k m) : Bonferroni B κ ε₀ k' m :=
  fun t Y h1 h2 h3 h4 => hB t Y h1 h2 h3 (by omega)

/-- **Theorem 4.5 as a reduction (`q = 7`).** In a generalized hexagon of order `(7, 7)` satisfying the
statements `Bonferroni` (Lemma 4.3, with `k = 4`) and `PerpBound` (Lemma 4.4) for the colour class `ε₀` of the unbarred
hubs, every geometric (twisted) labelling of Gómez's wiring, in every block pattern, gives a far pair. The
double count of the note (six forced perpendicular pairs at every row against `15 · 4144` in total) is proved
here. -/
theorem omega45_of_hyps [Nonempty β] (H : Hex B κ 7) {α : ℕ} (hα : 0 < α) (h2 : 2 * α ≤ 7 + 3)
    (typ : Fin α → Bool) {ε₀ : ZMod 2} (lam : Copy α → autSub B κ)
    (hP : PerpBound B κ ε₀ 4144) (hB : Bonferroni B κ ε₀ 4 140) :
    ∃ x y, (9 : ℕ∞) ≤ (omega B κ typ ε₀ (nfmk (fun c => (lam c : Equiv.Perm β)))).edist x y := by
  by_contra hno
  set c' := cstar typ hα with hc'
  obtain ⟨hD2, hF0⟩ := star7 typ hα h2
  set I := F0 typ 0 c' with hI
  set g : Copy α → autSub B κ := fun c => lam c' * (lam c)⁻¹ with hg
  set φ : β → Copy α → β := fun t c => ((g c : autSub B κ) : Equiv.Perm β) t with hφ
  have hcol_φ : ∀ t c, κ (φ t c) = κ t := fun t c => (g c).2.2 t
  have hcen4 : ∀ t, cen4 typ (fun c => (lam c : Equiv.Perm β)) t c' = I.image (φ t) := fun t => rfl
  -- (1) no coincidences at any row of colour `ε₀`
  have step1 : ∀ t, κ t = ε₀ → t ∉ I.image (φ t) ∧ Set.InjOn (φ t) I ∧ (I.image (φ t)).card = 5 := by
    intro t ht
    have h4 : ¬ ((I.image (φ t)).erase t).card ≤ 4 := fun h => hno (omega45_lemma42 H hα h2 typ lam ht h)
    have hle1 : ((I.image (φ t)).erase t).card ≤ (I.image (φ t)).card := Finset.card_erase_le
    have hle2 : (I.image (φ t)).card ≤ I.card := Finset.card_image_le
    have hα5 : α ≤ 5 := by omega
    have hS5 : (I.image (φ t)).card = 5 := by omega
    have hnot : t ∉ I.image (φ t) := by
      intro hm
      have := Finset.card_erase_of_mem hm
      omega
    refine ⟨hnot, ?_, hS5⟩
    exact Finset.card_image_iff.1 (by omega)
  -- (2) at every row of colour `ε₀`, at least six of the fifteen pairs are at distance `≤ 4`
  have step2 : ∀ t, κ t = ε₀ →
      8 ≤ 2 * (I.filter fun c => B.dist t (φ t c) ≤ 4).card +
        (I.offDiag.filter fun p => B.dist (φ t p.1) (φ t p.2) ≤ 4).card := by
    intro t ht
    obtain ⟨hnot, hinj, hS5⟩ := step1 t ht
    have hrad := fun h => hno (far_of_rad4 H (by norm_num) lam ht (cstar_not_mem typ hα) h)
    have hrad' : rad4 B typ (fun c => (lam c : Equiv.Perm β)) t c' =
        (I.image (φ t)).biUnion (fun y => ballOpp B t y 4) := rad4_eq _ _ _ _
    by_contra hlt
    push Not at hlt
    have hA : ((I.image (φ t)).filter fun y => B.dist t y ≤ 4).card =
        (I.filter fun c => B.dist t (φ t c) ≤ 4).card := by
      rw [Finset.filter_image, Finset.card_image_of_injOn (hinj.mono (Finset.coe_subset.2 (Finset.filter_subset _ _)))]
    have hBc : (((I.image (φ t)) ×ˢ (I.image (φ t))).filter fun p => p.1 ≠ p.2 ∧ B.dist p.1 p.2 ≤ 4).card =
        (I.offDiag.filter fun p => B.dist (φ t p.1) (φ t p.2) ≤ 4).card := by
      symm
      refine Finset.card_bij (fun p _ => (φ t p.1, φ t p.2)) ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_product, Finset.mem_image] at hp ⊢
        obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hp
        exact ⟨⟨⟨p.1, h1, rfl⟩, ⟨p.2, h2, rfl⟩⟩, fun he => h3 (hinj h1 h2 he), h4⟩
      · intro p hp p' hp' he
        simp only [Finset.mem_filter, Finset.mem_offDiag] at hp hp'
        have e1 := hinj hp.1.1 hp'.1.1 (Prod.mk.inj he).1
        have e2 := hinj hp.1.2.1 hp'.1.2.1 (Prod.mk.inj he).2
        exact Prod.ext e1 e2
      · rintro ⟨y1, y2⟩ hy
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image] at hy
        obtain ⟨⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩, hne, hd⟩ := hy
        refine ⟨(a, b), ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_offDiag]
        exact ⟨⟨ha, hb, fun he => hne (by rw [he])⟩, hd⟩
    have hprem := hB t (I.image (φ t)) ht hS5
      (fun y hy => by
        obtain ⟨c, hcI, rfl⟩ := Finset.mem_image.1 hy
        exact ⟨by rw [hcol_φ t c]; exact ht, fun he => hnot (Finset.mem_image.2 ⟨c, hcI, he⟩)⟩)
      (by rw [hA, hBc]; exact hlt)
    apply hrad
    rw [hrad']
    have : (D2 typ c').card * 7 ^ 2 ≤ 140 * 7 ^ 2 := Nat.mul_le_mul_right _ hD2
    omega
  -- (3) the double count over the rows of colour `ε₀`
  obtain ⟨t0, ht0⟩ := exists_row H ε₀
  set T : Finset β := univ.filter fun s => κ s = ε₀ with hT
  have hTcard : 7 ^ 5 ≤ T.card := by
    have h1 := q_pow_five_le_card_sph_six H.col H.deg H.girth H.reach (u := t0) (show 1 ≤ 7 by norm_num)
    have h2 : sph B t0 6 ⊆ T := by
      intro x hx
      rw [mem_sph] at hx
      rw [hT, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (col_opp H hx).symm.trans ht0⟩
    exact h1.trans (Finset.card_le_card h2)
  have hI5 : I.card = 5 := by
    obtain ⟨_, _, hS5⟩ := step1 t0 ht0
    have : (I.image (φ t0)).card ≤ I.card := Finset.card_image_le
    have : α ≤ 5 := by omega
    omega
  have hsum : T.card * 8 ≤ ∑ t ∈ T, (2 * (I.filter fun c => B.dist t (φ t c) ≤ 4).card +
      (I.offDiag.filter fun p => B.dist (φ t p.1) (φ t p.2) ≤ 4).card) := by
    calc T.card * 8 = ∑ t ∈ T, 8 := by simp
      _ ≤ _ := Finset.sum_le_sum fun t ht => step2 t (Finset.mem_filter.1 ht).2
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hS1 : ∑ t ∈ T, (I.filter fun c => B.dist t (φ t c) ≤ 4).card =
      ∑ c ∈ I, (PerpSet B κ ε₀ ((g c : autSub B κ) : Equiv.Perm β)).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.card_filter]
    congr 1
    ext t
    simp only [PerpSet, hT, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Iff.rfl
  have key : ∀ c e t, B.dist (φ t c) (φ t e) =
      B.dist t (((((g c)⁻¹ * g e : autSub B κ)) : Equiv.Perm β) t) := by
    intro c e t
    have := dist_aut H (g c)⁻¹ (φ t c) (φ t e)
    simpa [φ] using this.symm
  have hS2 : ∑ t ∈ T, (I.offDiag.filter fun p => B.dist (φ t p.1) (φ t p.2) ≤ 4).card =
      ∑ p ∈ I.offDiag, (PerpSet B κ ε₀ ((((g p.1)⁻¹ * g p.2 : autSub B κ)) : Equiv.Perm β)).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.card_filter]
    congr 1
    ext t
    simp only [PerpSet, hT, Finset.mem_filter, Finset.mem_univ, true_and, key]
  have hfix1 : ∀ c ∈ I, ∀ s, κ s = ε₀ → ((g c : autSub B κ) : Equiv.Perm β) s ≠ s := by
    intro c hc s hs he
    obtain ⟨hnot, _, _⟩ := step1 s hs
    exact hnot (Finset.mem_image.2 ⟨c, hc, he⟩)
  have hfix2 : ∀ p ∈ I.offDiag, ∀ s, κ s = ε₀ →
      ((((g p.1)⁻¹ * g p.2 : autSub B κ)) : Equiv.Perm β) s ≠ s := by
    intro p hp s hs he
    obtain ⟨_, hinj, _⟩ := step1 s hs
    rw [Finset.mem_offDiag] at hp
    apply hp.2.2
    apply hinj hp.1 hp.2.1
    have h1 : ((g p.1 : autSub B κ) : Equiv.Perm β) (((((g p.1)⁻¹ * g p.2 : autSub B κ)) : Equiv.Perm β) s) =
        ((g p.2 : autSub B κ) : Equiv.Perm β) s := by
      simp
    rw [he] at h1
    exact h1
  have hb1 : ∑ c ∈ I, (PerpSet B κ ε₀ ((g c : autSub B κ) : Equiv.Perm β)).card ≤ I.card * 4144 := by
    calc _ ≤ ∑ c ∈ I, 4144 := Finset.sum_le_sum fun c hc => hP (g c) (hfix1 c hc)
      _ = I.card * 4144 := by simp
  have hb2 : ∑ p ∈ I.offDiag, (PerpSet B κ ε₀ ((((g p.1)⁻¹ * g p.2 : autSub B κ)) : Equiv.Perm β)).card ≤
      I.offDiag.card * 4144 := by
    calc _ ≤ ∑ p ∈ I.offDiag, 4144 := Finset.sum_le_sum fun p hp => hP ((g p.1)⁻¹ * g p.2) (hfix2 p hp)
      _ = I.offDiag.card * 4144 := by simp
  have hoff : I.offDiag.card = 20 := by rw [Finset.offDiag_card, hI5]
  rw [hS1, hS2] at hsum
  rw [hI5] at hb1
  rw [hoff] at hb2
  norm_num at hTcard
  omega

end BipartiteDD.LeanMaxx.Omega45
