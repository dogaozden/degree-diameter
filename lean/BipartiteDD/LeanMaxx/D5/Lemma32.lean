import BipartiteDD.LeanMaxx.D5.ThmE

/-! # D = 5 formalisation, part 12: Lemma 3.2 and Definition 3.3 for the two-level graph

`research/theorems/D5_QUADRANGLE.md` Lemma 3.2: a path of length `≤ 5` from level `i` to level `j` that uses only
level edges of `i`, `j` and the remaining matching edges of the arc `i → j` uses exactly one matching edge. Here this
is shown in the form needed for Definition 3.3 (every vertex of level `i` is joined to every vertex of level `j`
by such a path of length `≤ 5`) ⟺ the route condition (3.1), i.e. `Data.Repaired`:

* `twoLevel D i j` is the graph on `Bool × (P ⊕ L)` (`false` = level `i`, `true` = level `j`) with the level edges and
  the matching edges `(a, false) ~ (M a, true)`, `a ∈ A_i ∖ R i j`;
* `Hyp.repaired_iff_reach`: `D.Repaired i j ↔ ∀ u v, Reach (twoLevel D i j) (false, u) (true, v) 5`.

Proof of the hard direction: a mutual induction on the length `n`. (CS) a walk of length `n ≤ 3` between two vertices of
one level gives a walk of length `n` in `I`; (CO) a walk of length `n ≤ 5` from level `i` to level `j` gives a route
`u ⇝ a → M a ⇝ v` with total length `≤ n`. A crossing edge is followed either by a walk back in the same level, or
by a walk that must retrace it, because two different elements of one colour are at distance `≥ 2`. -/

namespace BipartiteDD.LeanMaxx.D5

open SimpleGraph BipartiteDD

variable {P L : Type*} [Membership P L] {ι V U : Type*}

theorem reach_zero {W : Type*} {G : SimpleGraph W} {p q : W} (h : Reach G p q 0) : p = q := by
  obtain ⟨w, hw⟩ := h
  exact Walk.eq_of_length_eq_zero (by omega : w.length = 0)

theorem reach_cases {W : Type*} {G : SimpleGraph W} {p q : W} {n : ℕ} (h : Reach G p q (n + 1)) :
    p = q ∨ ∃ r, G.Adj p r ∧ Reach G r q n := by
  obtain ⟨w, hw⟩ := h
  cases w with
  | nil => exact Or.inl rfl
  | cons h w' => exact Or.inr ⟨_, h, ⟨w', by simp at hw; omega⟩⟩

/-- Two different elements of one colour are at distance at least two. -/
theorem reach_same' {x y : P ⊕ L} {n : ℕ} (hne : x ≠ y) (hc : col x = col y)
    (h : Reach (incGraph P L) x y n) : 2 ≤ n := by
  obtain ⟨w, hw⟩ := h
  have := (walk_same w hc hne).1
  omega

variable (D : Data P L ι V U) (i j : ι)

/-- The two-level graph of the arc `i → j` after deleting the freed matching edges. -/
def twoLevel : SimpleGraph (Bool × (P ⊕ L)) :=
  SimpleGraph.fromRel fun p q =>
    (p.1 = q.1 ∧ (incGraph P L).Adj p.2 q.2) ∨
      (p.1 = false ∧ q.1 = true ∧ col p.2 = D.τ i ∧ p.2 ∉ D.R i j ∧ q.2 = D.M i j p.2)

theorem twoLevel_adj_level {b : Bool} {x y : P ⊕ L} (h : (incGraph P L).Adj x y) :
    (twoLevel D i j).Adj (b, x) (b, y) :=
  (SimpleGraph.fromRel_adj _ _ _).2 ⟨by simpa using h.ne, Or.inl (Or.inl ⟨rfl, h⟩)⟩

theorem twoLevel_adj_cross {x : P ⊕ L} (hx : col x = D.τ i) (hR : x ∉ D.R i j) :
    (twoLevel D i j).Adj (false, x) (true, D.M i j x) :=
  (SimpleGraph.fromRel_adj _ _ _).2 ⟨by simp, Or.inl (Or.inr ⟨rfl, rfl, hx, hR, rfl⟩)⟩

/-- The adjacency relation of `twoLevel`, case by case. -/
theorem twoLevel_adj {p q : Bool × (P ⊕ L)} (h : (twoLevel D i j).Adj p q) :
    (p.1 = q.1 ∧ (incGraph P L).Adj p.2 q.2) ∨
    (p.1 = false ∧ q.1 = true ∧ col p.2 = D.τ i ∧ p.2 ∉ D.R i j ∧ q.2 = D.M i j p.2) ∨
    (q.1 = false ∧ p.1 = true ∧ col q.2 = D.τ i ∧ q.2 ∉ D.R i j ∧ p.2 = D.M i j q.2) := by
  rcases (SimpleGraph.fromRel_adj _ _ _).1 h with ⟨-, h' | h'⟩
  · rcases h' with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · rcases h' with h' | h'
    · exact Or.inl ⟨h'.1.symm, h'.2.symm⟩
    · exact Or.inr (Or.inr h')

namespace Hyp

variable {D} (H : Hyp D)
include H

/-- The core of Lemma 3.2 (mutual induction). -/
theorem lemma32_aux {i j : ι} (hT : D.T i j) : ∀ n : ℕ,
    (n ≤ 3 → ∀ (b : Bool) (x y : P ⊕ L), Reach (twoLevel D i j) (b, x) (b, y) n →
      Reach (incGraph P L) x y n) ∧
    (n ≤ 5 → ∀ x y : P ⊕ L, Reach (twoLevel D i j) (false, x) (true, y) n →
      ∃ a, col a = D.τ i ∧ a ∉ D.R i j ∧ ∃ m k : ℕ, m + 1 + k ≤ n ∧
        Reach (incGraph P L) x a m ∧ Reach (incGraph P L) (D.M i j a) y k) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have CO : ∀ n' < n, n' ≤ 5 → ∀ x y : P ⊕ L, Reach (twoLevel D i j) (false, x) (true, y) n' →
        ∃ a, col a = D.τ i ∧ a ∉ D.R i j ∧ ∃ m k : ℕ, m + 1 + k ≤ n' ∧
          Reach (incGraph P L) x a m ∧ Reach (incGraph P L) (D.M i j a) y k :=
      fun n' hn' => (ih n' hn').2
    have CS : ∀ n' < n, n' ≤ 3 → ∀ (b : Bool) (x y : P ⊕ L), Reach (twoLevel D i j) (b, x) (b, y) n' →
        Reach (incGraph P L) x y n' := fun n' hn' => (ih n' hn').1
    refine ⟨fun hn b x y h => ?_, fun hn x y h => ?_⟩
    · -- (CS)
      cases n with
      | zero =>
        have := reach_zero h
        simp only [Prod.mk.injEq, true_and] at this
        subst this; exact Reach.refl _ _
      | succ n =>
        rcases reach_cases h with he | ⟨r, hr, hrest⟩
        · have := congrArg Prod.snd he
          simp only at this
          subst this; exact Reach.refl _ _
        obtain ⟨b', r'⟩ := r
        rcases twoLevel_adj D i j hr with ⟨hb, hadj⟩ | ⟨hb1, hb2, hcol, hR, hr2⟩ | ⟨hb1, hb2, hcol, hR, hr2⟩
        · -- level step
          simp only at hb hadj
          subst hb
          exact ((Reach.adj hadj).trans (CS n (by omega) (by omega) _ _ _ hrest)).mono (by omega)
        · -- crossing `(false, x) → (true, M x)`, then a walk back to level `false`
          simp only at hb1 hb2 hcol hR hr2
          subst hb1; subst hb2; subst hr2
          obtain ⟨a, haA, haR, m, k, hmk, h1, h2⟩ := CO n (by omega) (by omega) y _ hrest.symm
          by_cases hax : a = x
          · subst hax
            exact h1.symm.mono (by omega)
          · exfalso
            have hne : D.M i j a ≠ D.M i j x := fun h => hax ((D.M i j).injective h)
            have hc : col (D.M i j a) = col (D.M i j x) := by
              rw [H.maps i j hT a haA, H.maps i j hT x hcol]
            have := reach_same' hne hc h2
            omega
        · -- crossing `(false, r') → (true, x)`, `x = M r'`, then a route back
          simp only at hb1 hb2 hcol hR hr2
          subst hb1; subst hb2; subst hr2
          obtain ⟨a, haA, haR, m, k, hmk, h1, h2⟩ := CO n (by omega) (by omega) r' y hrest
          by_cases hax : a = r'
          · subst hax
            exact h2.mono (by omega)
          · exfalso
            have hc : col r' = col a := by rw [hcol, haA]
            have := reach_same' hax hc.symm h1.symm
            omega
    · -- (CO)
      cases n with
      | zero =>
        have := reach_zero h
        simp at this
      | succ n =>
        rcases reach_cases h with he | ⟨r, hr, hrest⟩
        · simp at he
        obtain ⟨b', r'⟩ := r
        rcases twoLevel_adj D i j hr with ⟨hb, hadj⟩ | ⟨hb1, hb2, hcol, hR, hr2⟩ | ⟨hb1, hb2, hcol, hR, hr2⟩
        · simp only at hb hadj
          subst hb
          obtain ⟨a, haA, haR, m, k, hmk, h1, h2⟩ := CO n (by omega) (by omega) r' y hrest
          exact ⟨a, haA, haR, m + 1, k, by omega, ((Reach.adj hadj).trans h1).mono (by omega), h2⟩
        · simp only at hb1 hb2 hcol hR hr2
          subst hb2; subst hr2
          refine ⟨x, hcol, hR, 0, n, by omega, Reach.refl _ _, ?_⟩
          by_cases hn3 : n ≤ 3
          · exact CS n (by omega) hn3 true _ _ hrest
          · exact (H.base.all4 _ _).mono (by omega)
        · simp only at hb1 hb2
          simp at hb2

/-- Level `b` of the two-level graph is a copy of the incidence graph. -/
def twoLevelHom (b : Bool) : incGraph P L →g twoLevel D i j where
  toFun x := (b, x)
  map_rel' := fun h => twoLevel_adj_level D i j h

/-- **Definition 3.3 and Lemma 3.2.** The arc `i → j` is repaired in the sense of (3.1) iff every vertex of level `i`
is joined to every vertex of level `j` by a walk of length at most `5` in the two-level graph (level edges of `i`, `j`
and the remaining matching edges of the arc). -/
theorem repaired_iff_reach {i j : ι} (hT : D.T i j) :
    D.Repaired i j ↔ ∀ u v : P ⊕ L, Reach (twoLevel D i j) (false, u) (true, v) 5 := by
  constructor
  · intro hr u v
    obtain ⟨a, haA, haR, m, k, hmk, h1, h2⟩ := hr u v
    have e1 := h1.map (twoLevelHom (D := D) i j false)
    have e2 := Reach.adj (twoLevel_adj_cross D i j haA haR)
    have e3 := h2.map (twoLevelHom (D := D) i j true)
    exact ((e1.trans e2).trans e3).mono (by omega)
  · intro h u v
    obtain ⟨a, haA, haR, m, k, hmk, h1, h2⟩ := ((H.lemma32_aux hT 5).2 le_rfl u v (h u v))
    exact ⟨a, haA, haR, m, k, by omega, h1, h2⟩

/-- **Theorem E, graph form.** For a nonempty freed set, every vertex of level `i` is within `5` of every vertex of
level `j` in the two-level graph iff (E2) and (E3). -/
theorem reach_iff_E {i j : ι} (hT : D.T i j) (hRA : ∀ x ∈ D.R i j, col x = D.τ i)
    (hne : (D.R i j).Nonempty) :
    (∀ u v : P ⊕ L, Reach (twoLevel D i j) (false, u) (true, v) 5) ↔ D.E2 i j ∧ D.E3 i j :=
  (H.repaired_iff_reach hT).symm.trans (H.repaired_iff_E hT hRA hne)

end Hyp

end BipartiteDD.LeanMaxx.D5
