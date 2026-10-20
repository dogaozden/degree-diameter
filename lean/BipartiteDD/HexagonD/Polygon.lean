import BipartiteDD.Hexagon.Main

/-! Theorem D, slice 2, part 2: incidence-graph facts for a generalized hexagon.

For an incidence structure `inc : P → L → Prop` whose incidence graph is a generalized hexagon
(`GenPolygonGraph (Hexagon.incGraph inc) 6`):
* `Opp l₁ l₂` (no point of `l₁` is collinear with a point of `l₂`, including the case of a common point)
  is equivalent to the incidence graph distance between the lines being `6` (opposite lines);
* `eq_of_triangle`: no triangles, i.e. if a point `p ∉ v` lies on two lines `M₁`, `M₂` that both meet
  the line `v`, then `M₁ = M₂`. -/

namespace BipartiteDD.HexagonD

open SimpleGraph BipartiteDD.Hexagon BipartiteDD.Doubling

variable {P L : Type*} {inc : P → L → Prop}

/-- `l₁` and `l₂` are *far apart*: there is no point of `l₁` joined by a line (possibly `l₁` itself) to a
point of `l₂`. -/
def Opp (inc : P → L → Prop) (l₁ l₂ : L) : Prop :=
  ¬ ∃ (p : P) (M : L) (p' : P), inc p l₁ ∧ inc p M ∧ inc p' M ∧ inc p' l₂

theorem Opp.symm {l₁ l₂ : L} (h : Opp inc l₁ l₂) : Opp inc l₂ l₁ := by
  rintro ⟨p, M, p', h1, h2, h3, h4⟩
  exact h ⟨p', M, p, h4, h3, h2, h1⟩

/-- A walk of length at most `4` between two lines gives a "close" configuration. -/
theorem close_of_walk {l₁ l₂ : L} (w : (Hexagon.incGraph inc).Walk (.inr l₁) (.inr l₂)) (hw : w.length ≤ 4)
    (hl : ∃ p, inc p l₁) : ∃ (p : P) (M : L) (p' : P), inc p l₁ ∧ inc p M ∧ inc p' M ∧ inc p' l₂ := by
  cases w with
  | nil =>
    obtain ⟨p, hp⟩ := hl
    exact ⟨p, _, p, hp, hp, hp, hp⟩
  | cons h1 w1 =>
    rename_i b
    cases b with
    | inr l' => exact absurd h1 Hexagon.incGraph_not_adj_inr_inr
    | inl p =>
      have h1' : inc p l₁ := Hexagon.incGraph_adj_inr_inl.1 h1
      cases w1 with
      | cons h2 w2 =>
        rename_i b2
        cases b2 with
        | inl p2 => exact absurd h2 Hexagon.incGraph_not_adj_inl_inl
        | inr M =>
          have h2' : inc p M := Hexagon.incGraph_adj_inl_inr.1 h2
          cases w2 with
          | nil => exact ⟨p, l₁, p, h1', h1', h1', h2'⟩
          | cons h3 w3 =>
            rename_i b3
            cases b3 with
            | inr l'' => exact absurd h3 Hexagon.incGraph_not_adj_inr_inr
            | inl p' =>
              have h3' : inc p' M := Hexagon.incGraph_adj_inr_inl.1 h3
              cases w3 with
              | cons h4 w4 =>
                rename_i b4
                cases b4 with
                | inl p4 => exact absurd h4 Hexagon.incGraph_not_adj_inl_inl
                | inr M4 =>
                  have h4' : inc p' M4 := Hexagon.incGraph_adj_inl_inr.1 h4
                  cases w4 with
                  | nil => exact ⟨p, M, p', h1', h2', h3', h4'⟩
                  | cons h5 w5 =>
                    exfalso
                    simp only [Walk.length_cons] at hw
                    omega

theorem exists_point_of_deg {G : SimpleGraph (P ⊕ L)} (hdeg : ∀ v, ∃ a b, G.Adj v a ∧ G.Adj v b ∧ a ≠ b)
    (hG : G = Hexagon.incGraph inc) (l : L) : ∃ p, inc p l := by
  subst hG
  obtain ⟨a, b, ha, -, -⟩ := hdeg (.inr l)
  cases a with
  | inl p => exact ⟨p, Hexagon.incGraph_adj_inr_inl.1 ha⟩
  | inr l' => exact absurd ha Hexagon.incGraph_not_adj_inr_inr

theorem exists_point (hG : GenPolygonGraph (Hexagon.incGraph inc) 6) (l : L) : ∃ p, inc p l :=
  exists_point_of_deg hG.deg rfl l

/-- Opposite lines (no point of one collinear with a point of the other) are at distance `6`. -/
theorem edist_eq_six_of_opp (hG : GenPolygonGraph (Hexagon.incGraph inc) 6) {l₁ l₂ : L} (h : Opp inc l₁ l₂) :
    (Hexagon.incGraph inc).edist (.inr l₁) (.inr l₂) = 6 := by
  have hle : (Hexagon.incGraph inc).edist (.inr l₁) (.inr l₂) ≤ 6 := by
    have := edist_le_ediam (G := Hexagon.incGraph inc) (u := .inr l₁) (v := .inr l₂)
    rw [hG.ediam] at this
    exact_mod_cast this
  have hne : (Hexagon.incGraph inc).edist (.inr l₁) (.inr l₂) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) hle
  obtain ⟨w, hw⟩ := exists_walk_of_edist_ne_top hne
  have heven : Even w.length := (isLeft_eq_iff_even w).1 rfl
  have h6 : w.length ≤ 6 := by
    rw [← hw] at hle; exact_mod_cast hle
  have : w.length = 6 := by
    by_contra hne6
    have h4 : w.length ≤ 4 := by
      obtain ⟨k, hk⟩ := heven
      omega
    exact h (close_of_walk w h4 (exists_point hG l₁))
  rw [← hw, this]; rfl

/-- Conversely, lines at distance `6` are far apart. -/
theorem opp_of_edist_eq_six {l₁ l₂ : L} (h : (Hexagon.incGraph inc).edist (.inr l₁) (.inr l₂) = 6) :
    Opp inc l₁ l₂ := by
  rintro ⟨p, M, p', h1, h2, h3, h4⟩
  have := edist_le_of_walk (n := 4)
    (.cons (Hexagon.incGraph_adj_inr_inl.2 h1) (.cons (Hexagon.incGraph_adj_inl_inr.2 h2)
      (.cons (Hexagon.incGraph_adj_inr_inl.2 h3) (.cons (Hexagon.incGraph_adj_inl_inr.2 h4) .nil)) :
        (Hexagon.incGraph inc).Walk (.inl p) (.inr l₂)) :
        (Hexagon.incGraph inc).Walk (.inr l₁) (.inr l₂)) (by simp)
  rw [h] at this
  exact absurd this (by norm_num)

theorem opp_iff_edist_eq_six (hG : GenPolygonGraph (Hexagon.incGraph inc) 6) {l₁ l₂ : L} :
    Opp inc l₁ l₂ ↔ (Hexagon.incGraph inc).edist (.inr l₁) (.inr l₂) = 6 :=
  ⟨edist_eq_six_of_opp hG, opp_of_edist_eq_six⟩

/-! ### No triangles -/

theorem three_le_girth (hG : GenPolygonGraph (Hexagon.incGraph inc) 6) {a : P ⊕ L}
    (c : (Hexagon.incGraph inc).Walk a a) (hc : c.IsCycle) : 12 ≤ c.length := by
  have h2 := hc.egirth_le_length
  rw [hG.egirth] at h2
  exact_mod_cast h2

/-- Two lines through two distinct points coincide (no digons). -/
theorem eq_of_digon (hG : GenPolygonGraph (Hexagon.incGraph inc) 6) {p r : P} {M₁ M₂ : L} (hpr : p ≠ r)
    (h1 : inc p M₁) (h1' : inc r M₁) (h2 : inc p M₂) (h2' : inc r M₂) : M₁ = M₂ := by
  by_contra hne
  let c : (Hexagon.incGraph inc).Walk (.inl p) (.inl p) :=
    .cons (Hexagon.incGraph_adj_inl_inr.2 h1) (.cons (Hexagon.incGraph_adj_inr_inl.2 h1')
      (.cons (Hexagon.incGraph_adj_inl_inr.2 h2') (.cons (Hexagon.incGraph_adj_inr_inl.2 h2) .nil)))
  have hc : c.IsCycle := by
    simp [c, Walk.isCycle_def, Walk.isTrail_def, Walk.edges, Sym2.eq_iff, hpr, hpr.symm, hne,
      Ne.symm hne]
  have := three_le_girth hG c hc
  simp [c] at this

/-- No triangles: a point `p ∉ v` on two lines each meeting `v` lies on one such line only. -/
theorem eq_of_triangle (hG : GenPolygonGraph (Hexagon.incGraph inc) 6) {p p₁ p₂ : P} {v M₁ M₂ : L}
    (hp : ¬ inc p v) (h1 : inc p M₁) (h1' : inc p₁ M₁) (h1v : inc p₁ v) (h2 : inc p M₂)
    (h2' : inc p₂ M₂) (h2v : inc p₂ v) : M₁ = M₂ := by
  by_contra hne
  have hpp1 : p ≠ p₁ := fun h => hp (h ▸ h1v)
  have hpp2 : p ≠ p₂ := fun h => hp (h ▸ h2v)
  have hMv1 : M₁ ≠ v := fun h => hp (h ▸ h1)
  have hMv2 : M₂ ≠ v := fun h => hp (h ▸ h2)
  by_cases hp12 : p₁ = p₂
  · subst hp12
    exact hne (eq_of_digon hG hpp1 h1 h1' h2 h2')
  · let c : (Hexagon.incGraph inc).Walk (.inl p) (.inl p) :=
      .cons (Hexagon.incGraph_adj_inl_inr.2 h1) (.cons (Hexagon.incGraph_adj_inr_inl.2 h1')
        (.cons (Hexagon.incGraph_adj_inl_inr.2 h1v) (.cons (Hexagon.incGraph_adj_inr_inl.2 h2v)
          (.cons (Hexagon.incGraph_adj_inl_inr.2 h2') (.cons (Hexagon.incGraph_adj_inr_inl.2 h2) .nil)))))
    have hc : c.IsCycle := by
      simp [c, Walk.isCycle_def, Walk.isTrail_def, Walk.edges, Sym2.eq_iff, hpp1, hpp2, hp12,
        hne, hMv1, hMv2, Ne.symm hpp1, Ne.symm hpp2, Ne.symm hp12, Ne.symm hne, Ne.symm hMv1,
        Ne.symm hMv2]
    have := three_le_girth hG c hc
    simp [c] at this

end BipartiteDD.HexagonD
