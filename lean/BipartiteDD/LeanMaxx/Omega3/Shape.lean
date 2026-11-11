import BipartiteDD.LeanMaxx.Omega3.Route

/-!
# Shapes of short routes

In the normal form of Lemma 1.1 the marks are `mk false c = 1` (unbarred hubs sit on the same vertex in every
copy) and `mk true c = lam c`. A route from the copy `c₁` of `CuK 0` to the missed copy `c'` with total cost
`a + 2 |fn| ≤ 6` has at most three passes, and its endpoint lies in a ball around a *centre* `cen c d` with
`(c, d) ∈ F0 … F3` (`shape`). This is the case analysis of Lemma 2.1.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace BipartiteDD.LeanMaxx.Omega3

open Finset BipartiteDD.LeanMaxx.Omega2

variable {β : Type*} {α : ℕ}

/-- The normal-form marks of Lemma 1.1. -/
def nfmk (lam : Copy α → Equiv.Perm β) : Bool → Copy α → Equiv.Perm β := fun bar c => if bar then lam c else 1

theorem pT_false (lam : Copy α → Equiv.Perm β) (c d : Copy α) : pT (nfmk lam) false c d = 1 := by
  simp [pT, nfmk]

theorem pT_true (lam : Copy α → Equiv.Perm β) (c d : Copy α) : pT (nfmk lam) true c d = lam d * (lam c)⁻¹ := by
  simp [pT, nfmk]

/-- The centre of a barred pass from `c` to `d` applied to the row `t`. -/
def cen (lam : Copy α → Equiv.Perm β) (t : β) (c d : Copy α) : β := (lam d * (lam c)⁻¹) t

variable (typ : Fin α → Bool)

theorem share_of {bar : Bool} {c d : Copy α} (hne : c ≠ d)
    (hk : ∃ k, meets typ bar k c = true ∧ meets typ bar k d = true) : share typ bar c d = true := by
  simp [share, hne, hk]

theorem mem_F1 {k : ZMod 5} {c' x : Copy α} :
    x ∈ F1 typ k c' ↔ (∃ c₁ ∈ CuK typ k, share typ false c₁ x = true) ∧ share typ true x c' = true := by
  simp [F1]

theorem mem_F2 {k : ZMod 5} {c' : Copy α} {p : Copy α × Copy α} :
    p ∈ F2 typ k c' ↔ p.1 ∈ CuK typ k ∧ share typ true p.1 p.2 = true ∧ share typ false p.2 c' = true := by
  simp [F2]

theorem mem_F3 {k : ZMod 5} {c' c : Copy α} :
    c ∈ F3 typ k c' ↔ c ∈ CuK typ k ∧ ∃ x, share typ true c x = true ∧ share typ true x c' = true := by
  simp [F3]

/-- Covering of a vertex by the balls around the centres of `F0 … F3`. -/
def CovP (B : SimpleGraph β) (lam : Copy α → Equiv.Perm β) (t c'y : β) (c' : Copy α) : Prop :=
  (∃ c₁ ∈ F0 typ 0 c', B.dist (cen lam t c₁ c') c'y ≤ 4) ∨
  (∃ x ∈ F1 typ 0 c', B.dist (cen lam t x c') c'y ≤ 2) ∨
  (∃ p ∈ F2 typ 0 c', B.dist (cen lam t p.1 p.2) c'y ≤ 2) ∨
  (∃ c₁ ∈ F3 typ 0 c' \ F0 typ 0 c', B.dist (cen lam t c₁ c') c'y ≤ 2)

variable {typ} {B : SimpleGraph β} {lam : Copy α → Equiv.Perm β} {ε₀ : ZMod 2}

/-- **The shape of short routes.** A route from `c₁ ∈ CuK 0` to the missed copy `c'` of cost `≤ 6` whose
endpoint `y'` is far (`≥ 6`) from the hub row `t` ends in one of the balls of `CovP`. -/
theorem shape {t y' : β} {c₁ c' : Copy α} {fn : List (Bool × Copy α)} {a : ℕ}
    (hc₁ : c₁ ∈ CuK typ 0) (hc' : c' ∉ CuK typ 0)
    (hR : Route typ ε₀ ε₀ c₁ c' fn a) (hfa : a + 2 * fn.length ≤ 6)
    (hwB : ∃ wB : B.Walk (ev (nfmk lam) c₁ fn t) y', wB.length ≤ a) (hy' : 6 ≤ B.dist t y') :
    CovP typ B lam t y' c' := by
  obtain ⟨wB, hwB⟩ := hwB
  have hd : B.dist (ev (nfmk lam) c₁ fn t) y' ≤ a := (SimpleGraph.dist_le wB).trans hwB
  have hne : c₁ ≠ c' := fun h => hc' (h ▸ hc₁)
  -- the identity transformation cannot reach `y'`
  have hid : ev (nfmk lam) c₁ fn t = t → a ≤ 4 → False := by
    intro h h4
    rw [h] at hd; omega
  match fn, hR, hfa, hd, hid with
  | [], hR, _, _, _ => exact absurd hR hne
  | [(b, x)], hR, hfa, hd, hid =>
    simp only [Route] at hR
    obtain ⟨hcx, s, hs, hcol, hm, hr⟩ := hR
    have hxc : x = c' := hr
    subst hxc
    have hev : ev (nfmk lam) c₁ [(b, x)] = pT (nfmk lam) b c₁ x := by simp [ev]
    cases b
    · exfalso
      apply hid
      · rw [hev, pT_false]; rfl
      · simp at hfa; omega
    · left
      refine ⟨c₁, ?_, ?_⟩
      · rw [mem_F0]
        exact ⟨(mem_CuK typ).1 hc₁, share_of typ hne hm⟩
      · rw [hev, pT_true] at hd
        simp only [cen]
        have : a ≤ 4 := by simp at hfa; omega
        omega
  | [(b₁, x), (b₂, x₂)], hR, hfa, hd, hid =>
    simp only [Route] at hR
    obtain ⟨hcx, s₁, hs₁, hcol₁, hm₁, hx2, s₂, hs₂, hcol₂, hm₂, hr⟩ := hR
    have hxc : x₂ = c' := hr
    subst hxc
    have ha : a ≤ 2 := by simp at hfa; omega
    have hev : ev (nfmk lam) c₁ [(b₁, x), (b₂, x₂)] = pT (nfmk lam) b₂ x x₂ * pT (nfmk lam) b₁ c₁ x := by
      simp [ev]
    rw [hev] at hd hid
    cases b₁ <;> cases b₂
    · exfalso
      apply hid
      · simp [pT_false]
      · omega
    · -- (unbarred, barred): `x ∈ F1`
      right; left
      refine ⟨x, ?_, ?_⟩
      · rw [mem_F1]
        exact ⟨⟨c₁, hc₁, share_of typ hcx hm₁⟩, share_of typ hx2 hm₂⟩
      · simp only [pT_false, pT_true, mul_one] at hd
        simp only [cen]; omega
    · -- (barred, unbarred): `(c₁, x) ∈ F2`
      right; right; left
      refine ⟨(c₁, x), ?_, ?_⟩
      · rw [mem_F2]
        exact ⟨hc₁, share_of typ hcx hm₁, share_of typ hx2 hm₂⟩
      · simp only [pT_false, pT_true, one_mul] at hd
        simp only [cen]; omega
    · -- (barred, barred): the transformation telescopes to `λ_{c'} λ_{c₁}⁻¹`
      have htel : pT (nfmk lam) true x x₂ * pT (nfmk lam) true c₁ x = lam x₂ * (lam c₁)⁻¹ := by
        simp only [pT_true]; group
      rw [htel] at hd
      have hF3 : c₁ ∈ F3 typ 0 x₂ := by
        rw [mem_F3]
        exact ⟨hc₁, x, share_of typ hcx hm₁, share_of typ hx2 hm₂⟩
      by_cases h0 : c₁ ∈ F0 typ 0 x₂
      · left
        refine ⟨c₁, h0, ?_⟩
        simp only [cen]; omega
      · right; right; right
        refine ⟨c₁, Finset.mem_sdiff.2 ⟨hF3, h0⟩, ?_⟩
        simp only [cen]; omega
  | [(b₁, x₁), (b₂, x₂), (b₃, x₃)], hR, hfa, hd, hid =>
    simp only [Route] at hR
    obtain ⟨_, s₁, hs₁, hcol₁, _, _, s₂, hs₂, hcol₂, _, _, s₃, hs₃, hcol₃, _, _⟩ := hR
    have ha : a = 0 := by simp at hfa; omega
    subst ha
    have e1 : s₁ = 0 := by omega
    have e2 : s₂ = 0 := by omega
    have e3 : s₃ = 0 := by omega
    subst e1 e2 e3
    simp only [Nat.cast_zero, add_zero] at hcol₁ hcol₂ hcol₃
    have h1 : b₁ = false := hubcol_inj ε₀ (by rw [hubcol_false]; exact hcol₁.symm)
    have h2 : b₂ = false := hubcol_inj ε₀ (by rw [hubcol_false]; exact hcol₂.symm.trans hcol₁.symm)
    have h3 : b₃ = false :=
      hubcol_inj ε₀ (by rw [hubcol_false]; exact hcol₃.symm.trans (hcol₂.symm.trans hcol₁.symm))
    subst h1 h2 h3
    exfalso
    apply hid
    · simp [ev, pT_false]
    · omega
  | (_ :: _ :: _ :: _ :: fn), _, hfa, _, _ =>
    simp at hfa; omega

end BipartiteDD.LeanMaxx.Omega3
