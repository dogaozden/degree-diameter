import BipartiteDD.HexagonEven.Pi

/-! Theorem D (even `q`), the cubic (mirror of `HexagonD/GCubic.lean`, Lemma `G2` of `research/evenq/evenq.tex`).

For `d` with `t² + t + d ≠ 0` for all `t`, the cubic `G(a, b) = (c₀a + c₁b)(a² + ab + db²) + b³` has no zero on
`F² ∖ {0}` for suitable `c₀, c₁`, as soon as `|F| ≥ 4`. Proof: `G(t b, b) = b³((c₀t + c₁)(t²+t+d) + 1)` (`b ≠ 0`),
and `G(a, 0) = c₀a³`. Take `ω ∉ {0, 1}`, `c₀ = (r(ω) - r(0))/ω ≠ 0` with `r(t) = 1/(t²+t+d)`; then `t ↦ r(t) - c₀t`
is not injective (`0` and `ω` collide), so it misses some value `c₁`. -/

namespace BipartiteDD.HexagonEven

variable {F : Type*} [Field F]

/-- The cubic `G(a, b) = (c₀a + c₁b)(a² + ab + db²) + b³`. -/
def Gcub (d c0 c1 a b : F) : F := (c0 * a + c1 * b) * (a ^ 2 + a * b + d * b ^ 2) + b ^ 3

/-- `G` has no zero on `F² ∖ {0}`. -/
def GoodCubicE (d c0 c1 : F) : Prop := ∀ a b : F, ¬ (a = 0 ∧ b = 0) → Gcub d c0 c1 a b ≠ 0

theorem exists_nonzero_omega [Fintype F] (hq : 4 ≤ Fintype.card F) : ∃ ω : F, ω ≠ 0 ∧ ω ≠ 1 := by
  classical
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := fun x _ => by
    by_cases hx : x = 0
    · simp [hx]
    · simp [h x hx]
  have := Finset.card_le_card hsub
  have h01 : ({0, 1} : Finset F).card = 2 := Finset.card_pair zero_ne_one
  rw [h01, Finset.card_univ] at this
  omega

/-- **Lemma G2 (even `q ≥ 4`).** Under the anisotropy `t² + t + d ≠ 0`, there are `c₀, c₁` with `G` zero-free. -/
theorem exists_goodCubicE [Fintype F] {d : F} (hd : ∀ t : F, t ^ 2 + t + d ≠ 0) (hq : 4 ≤ Fintype.card F)
    (h2 : (2 : F) = 0) : ∃ c0 c1 : F, GoodCubicE d c0 c1 := by
  obtain ⟨ω, hω0, hω1⟩ := exists_nonzero_omega hq
  have hd0 : d ≠ 0 := by simpa using hd 0
  -- r(t) = 1 / (t² + t + d)
  let r : F → F := fun t => (t ^ 2 + t + d)⁻¹
  have hr0 : r 0 = d⁻¹ := by simp [r]
  have hrω : r ω ≠ r 0 := by
    intro h
    have e : ω ^ 2 + ω + d = d := by
      have := congrArg (fun y => y⁻¹) h
      simp only [r, inv_inv] at this
      simpa using this
    have hωω : ω * (ω + 1) = 0 := by linear_combination e
    rcases mul_eq_zero.1 hωω with h1 | h1
    · exact hω0 h1
    · exact hω1 (by linear_combination h1 - h2)
  -- c₀ = (r ω - r 0) / ω ≠ 0
  set c0 : F := (r ω - r 0) / ω with hc0
  have hc0ne : c0 ≠ 0 := div_ne_zero (sub_ne_zero.2 hrω) hω0
  -- the map t ↦ r t - c0 t is not injective (t = 0 and t = ω collide)
  let f : F → F := fun t => r t - c0 * t
  have hcω : c0 * ω = r ω - r 0 := by
    rw [hc0]
    field_simp
  have hf : f 0 = f ω := by
    simp only [f]
    rw [hcω]
    ring
  have hnsurj : ¬ Function.Surjective f := by
    intro hs
    have hinj := (Finite.injective_iff_surjective).2 hs
    exact hω0 (hinj hf).symm
  obtain ⟨c1, hc1⟩ : ∃ c1, ∀ t, c1 ≠ f t := by
    by_contra h
    push Not at h
    exact hnsurj (fun y => by obtain ⟨t, ht⟩ := h y; exact ⟨t, ht.symm⟩)
  refine ⟨c0, c1, ?_⟩
  intro a b hab
  by_cases hb : b = 0
  · subst hb
    have ha : a ≠ 0 := fun h => hab ⟨h, rfl⟩
    simp only [Gcub]
    have : c0 * a ^ 3 ≠ 0 := mul_ne_zero hc0ne (pow_ne_zero _ ha)
    intro h
    apply this
    linear_combination h
  · intro hG
    obtain ⟨t, rfl⟩ : ∃ t, a = t * b := ⟨a / b, by field_simp⟩
    -- G(t b, b) = b³ ((c0 t + c1)(t² + t + d) + 1)
    have key : (c0 * t + c1) * (t ^ 2 + t + d) + 1 = 0 := by
      have hb3 : b ^ 3 ≠ 0 := pow_ne_zero _ hb
      have : b ^ 3 * ((c0 * t + c1) * (t ^ 2 + t + d) + 1) = 0 := by
        simp only [Gcub] at hG
        linear_combination hG
      exact (mul_eq_zero.1 this).resolve_left hb3
    apply hc1 t
    -- c1 = r t - c0 t  (from key: (c0 t + c1) = -1 / (t²+t+d) = r t, using -1 = 1)
    have h1 : c0 * t + c1 = (t ^ 2 + t + d)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      linear_combination key - h2
    simp only [f, r]
    linear_combination h1

end BipartiteDD.HexagonEven
