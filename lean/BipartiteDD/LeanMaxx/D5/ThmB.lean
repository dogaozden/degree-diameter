import BipartiteDD.LeanMaxx.D5.ThmE

/-! # D = 5 formalisation, part 8: Theorem B (automorphic transitions)

`research/theorems/D5_QUADRANGLE.md` §5. A transition is *automorphic* if `M i j` agrees on `A_i` with an
automorphism `ψ` of the incidence graph `I`. Then it is repaired **if and only if** its freed set is a
partial ovoid (if `A_i` = points) or a partial spread (if `A_i` = lines), i.e. `R i j` has no two different
elements at distance two (`¬ Co x y`).

This needs the uniqueness half of the quadrangle axiom, which `GQst` does not record: `Strong` collects it
(two different elements have at most one common neighbour; an element `y` and a non-adjacent element `x` of the
other colour: at most one neighbour of `y` is at distance two from `x`). `GQst.strong` derives `Strong` from the
axioms and the point-line uniqueness hypothesis `uniq` used already in `GQ.card_points`. -/

namespace BipartiteDD.LeanMaxx.D5

open SimpleGraph BipartiteDD

variable {P L : Type*} [Membership P L] {ι V U : Type*}

/-- The base facts plus the uniqueness half of the quadrangle axiom (F4). -/
structure Strong (P L : Type*) [Membership P L] : Prop extends Base P L where
  cn : ∀ x y c w : P ⊕ L, x ≠ y → (incGraph P L).Adj x c → (incGraph P L).Adj y c →
    (incGraph P L).Adj x w → (incGraph P L).Adj y w → c = w
  uniq : ∀ x y : P ⊕ L, col x ≠ col y → ¬ (incGraph P L).Adj x y → ∀ z z' : P ⊕ L,
    (incGraph P L).Adj y z → (incGraph P L).Adj y z' → Co x z → Co x z' → z = z'

/-- `Co` is preserved by isomorphisms of the incidence graph. -/
theorem Co.map_iff (ψ : incGraph P L ≃g incGraph P L) {x y : P ⊕ L} : Co (ψ x) (ψ y) ↔ Co x y := by
  constructor
  · rintro ⟨hne, z, h1, h2⟩
    refine ⟨fun h => hne (by rw [h]), ψ.symm z, ?_, ?_⟩
    · rw [← ψ.map_adj_iff]; simpa using h1
    · rw [← ψ.map_adj_iff]; simpa using h2
  · rintro ⟨hne, z, h1, h2⟩
    exact ⟨fun h => hne (ψ.injective h), ψ z, ψ.map_adj_iff.2 h1, ψ.map_adj_iff.2 h2⟩

end BipartiteDD.LeanMaxx.D5

namespace BipartiteDD.GQst

open SimpleGraph BipartiteDD BipartiteDD.LeanMaxx.D5

variable {P L : Type*} [Membership P L] {s t : ℕ}

/-- The derived dual form of the uniqueness half. -/
theorem strong (G : GQst P L (s + 1) (t + 1))
    (uniq : ∀ (p : P) (l : L), p ∉ l → ∀ x y : P, x ∈ l → y ∈ l →
      (∃ m : L, p ∈ m ∧ x ∈ m) → (∃ m : L, p ∈ m ∧ y ∈ m) → x = y) : Strong P L where
  toBase := G.base
  cn := by
    rintro (p | l) (r | m) (c | d) (w | e) hne h1 h2 h3 h4
    all_goals first
      | (exfalso; exact incGraph_not_adj_inl_inl h1)
      | (exfalso; exact incGraph_not_adj_inr_inr h1)
      | (exfalso; exact incGraph_not_adj_inl_inl h2)
      | (exfalso; exact incGraph_not_adj_inr_inr h2)
      | (exfalso; exact incGraph_not_adj_inl_inl h3)
      | (exfalso; exact incGraph_not_adj_inr_inr h3)
      | (exfalso; exact incGraph_not_adj_inl_inl h4)
      | (exfalso; exact incGraph_not_adj_inr_inr h4)
      | skip
    · -- two points `p, r`, two lines `d, e` through both
      have h1' := incGraph_adj_inl_inr.1 h1
      have h2' := incGraph_adj_inl_inr.1 h2
      have h3' := incGraph_adj_inl_inr.1 h3
      have h4' := incGraph_adj_inl_inr.1 h4
      rcases G.one_line p r d e h1' h2' h3' h4' with h | h
      · exact absurd (congrArg Sum.inl h) hne
      · rw [h]
    · -- two lines `l, m`, two points `c, w` on both
      have h1' := incGraph_adj_inr_inl.1 h1
      have h2' := incGraph_adj_inr_inl.1 h2
      have h3' := incGraph_adj_inr_inl.1 h3
      have h4' := incGraph_adj_inr_inl.1 h4
      rcases G.one_line c w l m h1' h3' h2' h4' with h | h
      · rw [h]
      · exact absurd (congrArg Sum.inr h) hne
  uniq := by
    rintro (p | l) (r | m) hc hnadj z z' hz hz' hxz hxz'
    · simp [col] at hc
    · -- point `p`, line `m`, points `z, z'` on `m` collinear with `p`
      rcases z with z | z
      · rcases z' with z' | z'
        · have hzm := incGraph_adj_inr_inl.1 hz
          have hz'm := incGraph_adj_inr_inl.1 hz'
          have hpm : p ∉ m := fun h => hnadj (incGraph_adj_inl_inr.2 h)
          obtain ⟨-, a, ha1, ha2⟩ := hxz
          obtain ⟨-, a', ha1', ha2'⟩ := hxz'
          rcases a with a | a
          · exact absurd ha1 incGraph_not_adj_inl_inl
          rcases a' with a' | a'
          · exact absurd ha1' incGraph_not_adj_inl_inl
          exact congrArg Sum.inl (uniq p m hpm z z' hzm hz'm
            ⟨a, incGraph_adj_inl_inr.1 ha1, incGraph_adj_inr_inl.1 ha2⟩
            ⟨a', incGraph_adj_inl_inr.1 ha1', incGraph_adj_inr_inl.1 ha2'⟩)
        · exact absurd hz' incGraph_not_adj_inr_inr
      · exact absurd hz incGraph_not_adj_inr_inr
    · -- line `l`, point `r`, lines `z, z'` through `r` concurrent with `l`
      rcases z with z | z
      · exact absurd hz incGraph_not_adj_inl_inl
      · rcases z' with z' | z'
        · exact absurd hz' incGraph_not_adj_inl_inl
        · have hrz := incGraph_adj_inl_inr.1 hz
          have hrz' := incGraph_adj_inl_inr.1 hz'
          have hrl : r ∉ l := fun h => hnadj (incGraph_adj_inr_inl.2 h)
          obtain ⟨-, a, ha1, ha2⟩ := hxz
          obtain ⟨-, a', ha1', ha2'⟩ := hxz'
          rcases a with a | a
          swap
          · exact absurd ha1 incGraph_not_adj_inr_inr
          rcases a' with a' | a'
          swap
          · exact absurd ha1' incGraph_not_adj_inr_inr
          have hal := incGraph_adj_inr_inl.1 ha1
          have hal' := incGraph_adj_inr_inl.1 ha1'
          have haz := incGraph_adj_inl_inr.1 ha2
          have haz' := incGraph_adj_inl_inr.1 ha2'
          have haa : a = a' := uniq r l hrl a a' hal hal' ⟨z, hrz, haz⟩ ⟨z', hrz', haz'⟩
          subst haa
          have hra : r ≠ a := fun h => hrl (h ▸ hal)
          rcases G.one_line r a z z' hrz haz hrz' haz' with h | h
          · exact absurd h hra
          · exact congrArg Sum.inr h
    · simp [col] at hc

end BipartiteDD.GQst

namespace BipartiteDD.LeanMaxx.D5

open SimpleGraph BipartiteDD

variable {P L : Type*} [Membership P L] {ι V U : Type*}

/-- The common form of (E2) and (E3) for an automorphic transition. -/
def Data.Star (D : Data P L ι V U) (i j : ι) : Prop :=
  ∀ x ∈ D.R i j, ∀ w : P ⊕ L, col w = !D.τ i → ∃ a, a ∉ D.R i j ∧ Co x a ∧ (incGraph P L).Adj w a

namespace Hyp

variable {D : Data P L ι V U} (H : Hyp D)
include H

/-- An automorphism `ψ` of `I` that agrees with `M i j` on `A_i`: it maps `B_i` onto `A_j`. -/
theorem psi_B {i j : ι} (hT : D.T i j) (ψ : incGraph P L ≃g incGraph P L)
    (hψ : ∀ x, col x = D.τ i → D.M i j x = ψ x) {w : P ⊕ L} (hw : col w = !D.τ i) : col (ψ w) = D.τ j := by
  obtain ⟨z, -, -, hz, -⟩ := H.base.two w
  have hzc : col z = D.τ i := by
    rw [col_adj_not hz.symm, hw]; cases D.τ i <;> simp
  have h1 := H.maps i j hT z hzc
  rw [hψ z hzc] at h1
  have := col_adj_not (ψ.map_adj_iff.2 hz)
  rw [this, h1]; cases D.τ j <;> simp

theorem psi_symm_B {i j : ι} (hT : D.T i j) (ψ : incGraph P L ≃g incGraph P L)
    (hψ : ∀ x, col x = D.τ i → D.M i j x = ψ x) {y : P ⊕ L} (hy : col y = D.τ j) :
    col (ψ.symm y) = !D.τ i := by
  by_contra hcon
  have hA : col (ψ.symm y) = D.τ i := by
    cases h1 : col (ψ.symm y) <;> cases h2 : D.τ i <;> simp_all
  have h1 := H.maps i j hT _ hA
  rw [hψ _ hA] at h1
  simp only [RelIso.apply_symm_apply] at h1
  rw [hy] at h1
  cases D.τ j <;> simp at h1

theorem E2_iff_star {i j : ι} (hT : D.T i j) (hRA : ∀ x ∈ D.R i j, col x = D.τ i)
    (ψ : incGraph P L ≃g incGraph P L)
    (hψ : ∀ x, col x = D.τ i → D.M i j x = ψ x) : D.E2 i j ↔ D.Star i j := by
  constructor
  · intro h x hx w hw
    obtain ⟨a, hco, haR, hadj⟩ := h x hx (ψ w) (H.psi_B hT ψ hψ hw)
    have haA : col a = D.τ i := by rw [← hco.col_eq, hRA x hx]
    rw [hψ a haA] at hadj
    exact ⟨a, haR, hco, (ψ.map_adj_iff.1 hadj).symm⟩
  · intro h x hx y hy
    obtain ⟨a, haR, hco, hadj⟩ := h x hx (ψ.symm y) (H.psi_symm_B hT ψ hψ hy)
    have haA : col a = D.τ i := by rw [← hco.col_eq, hRA x hx]
    refine ⟨a, hco, haR, ?_⟩
    rw [hψ a haA]
    have := ψ.map_adj_iff.2 hadj
    simp only [RelIso.apply_symm_apply] at this
    exact this.symm

theorem E3_iff_star {i j : ι} (hT : D.T i j) (hRA : ∀ x ∈ D.R i j, col x = D.τ i)
    (ψ : incGraph P L ≃g incGraph P L)
    (hψ : ∀ x, col x = D.τ i → D.M i j x = ψ x) : D.E3 i j ↔ D.Star i j := by
  constructor
  · intro h x hx w hw
    obtain ⟨a, haR, hadj, hco⟩ := h x hx w hw
    have haA : col a = D.τ i := by
      rw [col_adj_not hadj.symm, hw]; cases D.τ i <;> simp
    rw [hψ a haA, hψ x (hRA x hx), Co.map_iff] at hco
    exact ⟨a, haR, hco, hadj⟩
  · intro h x hx w hw
    obtain ⟨a, haR, hco, hadj⟩ := h x hx w hw
    have haA : col a = D.τ i := by
      rw [col_adj_not hadj.symm, hw]; cases D.τ i <;> simp
    refine ⟨a, haR, hadj, ?_⟩
    rw [hψ a haA, hψ x (hRA x hx), Co.map_iff]
    exact hco

/-- `Star` ⟺ the freed set has no two elements at distance two (needs the uniqueness half). -/
theorem star_iff (Sg : Strong P L) {i j : ι} (hRA : ∀ x ∈ D.R i j, col x = D.τ i) :
    D.Star i j ↔ ∀ x ∈ D.R i j, ∀ y ∈ D.R i j, x ≠ y → ¬ Co x y := by
  constructor
  · intro h x hx y hy hxy hco
    obtain ⟨c, hc1, hc2⟩ := hco.2
    -- a neighbour `w` of `y` other than `c`
    obtain ⟨y1, y2, hne, h1, h2⟩ := Sg.two y
    have : ∃ w, (incGraph P L).Adj y w ∧ w ≠ c := by
      by_cases e : y1 = c
      · exact ⟨y2, h2, fun h => hne (e.trans h.symm)⟩
      · exact ⟨y1, h1, e⟩
    obtain ⟨w, hyw, hwc⟩ := this
    have hwcol : col w = !D.τ i := by rw [col_adj_not hyw.symm, hRA y hy]
    obtain ⟨a, haR, hxa, hwa⟩ := h x hx w hwcol
    have hcx : col x ≠ col w := by rw [hRA x hx, hwcol]; cases D.τ i <;> simp
    have hnadj : ¬ (incGraph P L).Adj x w := by
      intro hxw
      exact hwc (Sg.cn x y c w hxy hc1 hc2.symm hxw hyw).symm
    have hxy' : Co x y := hco
    have := Sg.uniq x w hcx hnadj y a hyw.symm hwa hxy' hxa
    exact haR (this ▸ hy)
  · intro h x hx w hw
    obtain ⟨z, hxz, hzw⟩ := Sg.cover x w (by rw [hRA x hx, hw]; cases D.τ i <;> simp)
    refine ⟨z, fun hz => h x hx z hz hxz.1 hxz, hxz, hzw.symm⟩

/-- The easy half of `star_iff`, which needs only the base facts. -/
theorem star_of_partial {i j : ι} (hRA : ∀ x ∈ D.R i j, col x = D.τ i)
    (h : ∀ x ∈ D.R i j, ∀ y ∈ D.R i j, x ≠ y → ¬ Co x y) : D.Star i j := by
  intro x hx w hw
  obtain ⟨z, hxz, hzw⟩ := H.base.cover x w (by rw [hRA x hx, hw]; cases D.τ i <;> simp)
  exact ⟨z, fun hz => h x hx z hz hxz.1 hxz, hxz, hzw.symm⟩

/-- **Theorem B, sufficiency** (base facts only): an automorphic transition whose freed set has no two elements
at distance two is repaired. -/
theorem repaired_of_partial {i j : ι} (hT : D.T i j)
    (hRA : ∀ x ∈ D.R i j, col x = D.τ i) (ψ : incGraph P L ≃g incGraph P L)
    (hψ : ∀ x, col x = D.τ i → D.M i j x = ψ x)
    (h : ∀ x ∈ D.R i j, ∀ y ∈ D.R i j, x ≠ y → ¬ Co x y) : D.Repaired i j := by
  by_cases hne : (D.R i j).Nonempty
  · have hs := H.star_of_partial hRA h
    exact H.repaired_of_E hT hRA hne ((H.E2_iff_star hT hRA ψ hψ).2 hs) ((H.E3_iff_star hT hRA ψ hψ).2 hs)
  · exact H.repaired_of_empty hT (Set.not_nonempty_iff_eq_empty.1 hne)

/-- **Theorem B.** An automorphic transition is repaired iff its freed set has no two elements at
distance two (a partial ovoid if `A_i` consists of points, a partial spread if of lines). -/
theorem repaired_iff_partial (Sg : Strong P L) {i j : ι} (hT : D.T i j)
    (hRA : ∀ x ∈ D.R i j, col x = D.τ i) (ψ : incGraph P L ≃g incGraph P L)
    (hψ : ∀ x, col x = D.τ i → D.M i j x = ψ x) :
    D.Repaired i j ↔ ∀ x ∈ D.R i j, ∀ y ∈ D.R i j, x ≠ y → ¬ Co x y := by
  by_cases hne : (D.R i j).Nonempty
  · rw [H.repaired_iff_E hT hRA hne, H.E2_iff_star hT hRA ψ hψ, H.E3_iff_star hT hRA ψ hψ,
      and_self, H.star_iff Sg hRA]
  · have hR : D.R i j = ∅ := Set.not_nonempty_iff_eq_empty.1 hne
    constructor
    · intro _ x hx; simp [hR] at hx
    · intro _; exact H.repaired_of_empty hT hR

end Hyp

end BipartiteDD.LeanMaxx.D5
