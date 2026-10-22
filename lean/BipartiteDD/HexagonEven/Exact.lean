import BipartiteDD.HexagonEven.PiZ
import BipartiteDD.HexagonEven.JLine
import BipartiteDD.HexagonEven.KeyId
import BipartiteDD.HexagonEven.GCubic
import BipartiteDD.HexagonEven.Levels
import BipartiteDD.HexagonEven.Spread

/-! Theorem D (even `q`), the exact whisker set (mirror of `HexagonD/Exact.lean` and `FreeLines.lean`).

`vStd = ⟨e₁, e₆⟩`, `nuE d x = (x₂x₃ + x₂x₄ + x₄x₅)/(d x₂² + x₂x₅ + x₅²)`, `Fz d c0 c1 z = G(z)/(α² + αβ + dβ²)`
with `G = Gcub`, and `Wset d c0 c1` the lines `m ≠ v` of some `S_z`, `z ≠ 0`, whose point in `Π` has `ν = F(z)`.

Exactness (`exists_unique_wline_even`): for a free point `p` with normalised representative `u` (`λ(u) = 1`,
`Q(u) = 0`), the lines of `S_z` through `u` are `⟨u, J_z u⟩` for `z` on the line `A_u : αu₂ + βu₅ = 1`; the point
`X_z = γu + J_z u` (`γ = λ(J_z u)`) is the `Π`-point of that line, and the key identity gives
`ν(X_z) = Φ(z) := N(z)/Θ + β³/D₂`. The condition `ν = F(z)` becomes `Ψ(z) = 0` with `Ψ` affine along `A_u`
with slope `G(u₅, u₂)/Θ ≠ 0`, so it has exactly one solution. -/

set_option linter.unusedSectionVars false

namespace BipartiteDD.HexagonEven

open BipartiteDD.Hexagon BipartiteDD.HexagonD Module Submodule

variable {F : Type*} [Field F]

/-! ### The line `v = ⟨e₁, e₆⟩` -/

theorem e1_ne' : (Pi.single 1 1 : V7 F) ≠ 0 := by
  intro h
  have := congr_fun h 1
  simp at this

theorem e1e6_pair' : IsHPair (Pi.single 1 1 : V7 F) (Pi.single 6 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Qf, Bf, Tits, pl, Pi.single_apply]

theorem e6_not_mem' : (Pi.single 6 1 : V7 F) ∉ span F {(Pi.single 1 1 : V7 F)} := by
  intro h
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 h
  have := congr_fun ha 6
  simp at this

/-- The line `v = ⟨e₁, e₆⟩`. -/
def vStd' : HLine F := hlineOf e1_ne' e1e6_pair' e6_not_mem'

theorem mem_vStd' {x : V7 F} : x ∈ (vStd' : HLine F).1 ↔
    x 0 = 0 ∧ x 2 = 0 ∧ x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0 := by
  constructor
  · intro hx
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hx
    simp [Pi.single_apply]
  · rintro ⟨h0, h2, h3, h4, h5⟩
    refine Submodule.mem_span_pair.2 ⟨x 1, x 6, ?_⟩
    ext i
    fin_cases i <;> simp [Pi.single_apply, *]

theorem vStd'_Pi (d : F) : ∀ x ∈ (vStd' : HLine F).1, x 0 + x 3 + d * x 4 = 0 := by
  intro x hx
  obtain ⟨h0, -, h3, h4, -⟩ := mem_vStd'.1 hx
  simp [*]

theorem vStd'_PiZ (d α β : F) : ∀ x ∈ (vStd' : HLine F).1, InPiZE d α β x := by
  intro x hx
  obtain ⟨h0, h2, h3, h4, h5⟩ := mem_vStd'.1 hx
  unfold InPiZE
  simp [*]

/-- The spread line `v` as a point of `S_d`. -/
def vS' (d : F) : SLineE d := ⟨vStd', vStd'_Pi d⟩

/-! ### The whisker set -/

/-- `ν(x) = (x₂x₃ + x₂x₄ + x₄x₅)/(d x₂² + x₂x₅ + x₅²)`. -/
def nuE (d : F) (x : V7 F) : F :=
  (x 2 * x 3 + x 2 * x 4 + x 4 * x 5) / (d * x 2 ^ 2 + x 2 * x 5 + x 5 ^ 2)

/-- `G(a, b) = (c₀a + c₁b)(a² + ab + db²) + b³`. -/
theorem Gcub_eq (d c0 c1 a b : F) : Gcub d c0 c1 a b = (c0 * a + c1 * b) * (a ^ 2 + a * b + d * b ^ 2) + b ^ 3 := rfl

/-- `F(z) = G(z)/(α² + αβ + dβ²)`. -/
def Fz (d c0 c1 : F) (z : F × F) : F := Gcub d c0 c1 z.1 z.2 / (z.1 ^ 2 + z.1 * z.2 + d * z.2 ^ 2)

/-- The exact whisker set. -/
def Wset (d c0 c1 : F) : Set (HLine F) :=
  {m | m ≠ vStd' ∧ ∃ z : F × F, z ≠ (0, 0) ∧ (∀ x ∈ m.1, InPiZE d z.1 z.2 x) ∧
    ∃ x ∈ m.1, x ≠ 0 ∧ x 0 + x 3 + d * x 4 = 0 ∧ nuE d x = Fz d c0 c1 z}

theorem nuE_smul (d : F) {b : F} (hb : b ≠ 0) (x : V7 F) : nuE d (b • x) = nuE d x := by
  unfold nuE
  simp only [Pi.smul_apply, smul_eq_mul]
  have h1 : b * x 2 * (b * x 3) + b * x 2 * (b * x 4) + b * x 4 * (b * x 5) =
      b ^ 2 * (x 2 * x 3 + x 2 * x 4 + x 4 * x 5) := by ring
  have h2 : d * (b * x 2) ^ 2 + b * x 2 * (b * x 5) + (b * x 5) ^ 2 =
      b ^ 2 * (d * x 2 ^ 2 + x 2 * x 5 + x 5 ^ 2) := by ring
  rw [h1, h2, mul_div_mul_left _ _ (pow_ne_zero 2 hb)]

theorem Fz_eq (d c0 c1 : F) (z : F × F) (hD : z.1 ^ 2 + z.1 * z.2 + d * z.2 ^ 2 ≠ 0) :
    Fz d c0 c1 z = (c0 * z.1 + c1 * z.2) + z.2 ^ 3 / (z.1 ^ 2 + z.1 * z.2 + d * z.2 ^ 2) := by
  unfold Fz
  rw [Gcub_eq, add_div, mul_div_cancel_right₀ _ hD]

theorem exists_ker_vec' (w : HLine F) (f : V7 F →ₗ[F] F) : ∃ x ∈ w.1, x ≠ 0 ∧ f x = 0 := by
  let g : w.1 →ₗ[F] F := f.comp w.1.subtype
  have h1 : finrank F (LinearMap.range g) + finrank F (LinearMap.ker g) = 2 := by
    have := LinearMap.finrank_range_add_finrank_ker g
    rw [w.2.1] at this
    exact this
  have h2 : finrank F (LinearMap.range g) ≤ 1 := by
    simpa using Submodule.finrank_le (LinearMap.range g)
  have h3 : 0 < finrank F (LinearMap.ker g) := by omega
  have hne : LinearMap.ker g ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at h3
    exact lt_irrefl _ h3
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨v.1, v.2, fun h => hv0 (Subtype.ext h), by simpa [g, LinearMap.mem_ker] using hv⟩

/-- `D₂ = α² + αβ + dβ² ≠ 0` for `(α, β) ≠ 0`. -/
theorem D2_ne {d : F} (hd : ∀ t : F, t ^ 2 + t + d ≠ 0) {z : F × F} (hz : z ≠ (0, 0)) :
    z.1 ^ 2 + z.1 * z.2 + d * z.2 ^ 2 ≠ 0 := by
  intro h
  by_cases hb : z.2 = 0
  · have ha : z.1 ≠ 0 := fun ha => hz (Prod.ext ha hb)
    rw [hb] at h
    apply ha
    have : z.1 ^ 2 = 0 := by linear_combination h
    exact pow_eq_zero_iff two_ne_zero |>.1 this
  · apply hd (z.1 / z.2)
    have : (z.1 / z.2) ^ 2 + z.1 / z.2 + d = (z.1 ^ 2 + z.1 * z.2 + d * z.2 ^ 2) / z.2 ^ 2 := by
      field_simp
    rw [this, h, zero_div]

/-- A line of `S_d` (in `Π_z`, `z ≠ 0`) lying in `Π_d` is `v`. -/
theorem no_second_line' {d : F} (hd : ∀ t : F, t ^ 2 + t + d ≠ 0) (h2 : (2 : F) = 0) {z : F × F}
    (hz : z ≠ (0, 0)) {w : HLine F} (hw : ∀ x ∈ w.1, InPiZE d z.1 z.2 x)
    (hw' : ∀ x ∈ w.1, x 0 + x 3 + d * x 4 = 0) : w = vStd' := by
  have hD := D2_ne hd hz
  let f : V7 F →ₗ[F] F := (d * z.2) • (LinearMap.proj 2 : V7 F →ₗ[F] F) +
    (z.1 + z.2) • (LinearMap.proj 5 : V7 F →ₗ[F] F)
  obtain ⟨x, hxw, hx0, hfx⟩ := exists_ker_vec' w f
  have hfx' : d * z.2 * x 2 + (z.1 + z.2) * x 5 = 0 := by simpa [f] using hfx
  have hL : x 0 + x 3 + d * x 4 = 0 := hw' x hxw
  have hLz : x 0 + x 3 + d * x 4 + z.1 * x 2 + z.2 * x 5 = 0 := hw x hxw
  have E1 : z.1 * x 2 + z.2 * x 5 = 0 := by linear_combination hLz - hL
  have hx2 : x 2 = 0 := by
    have : (z.1 ^ 2 + z.1 * z.2 + d * z.2 ^ 2) * x 2 = 0 := by
      linear_combination (z.1 + z.2) * E1 - z.2 * hfx' + (d * z.2 ^ 2 * x 2) * h2
    exact (mul_eq_zero.1 this).resolve_left hD
  have hx5 : x 5 = 0 := by
    have : (z.1 ^ 2 + z.1 * z.2 + d * z.2 ^ 2) * x 5 = 0 := by
      linear_combination z.1 * hfx' - (d * z.2) * E1 + (d * z.2 ^ 2 * x 5) * h2
    exact (mul_eq_zero.1 this).resolve_left hD
  have hQx : Qf x = 0 := Qf_eq_zero_of_mem_hline w hxw
  have hx0' : x 0 = -x 3 - d * x 4 := by linear_combination hL
  have hnum : x 3 ^ 2 + x 3 * x 4 + d * x 4 ^ 2 = 0 := by
    simp only [Qf] at hQx
    rw [hx2, hx5, hx0'] at hQx
    linear_combination -hQx
  have h4 : x 4 = 0 := by
    by_contra h4
    apply hd (x 3 / x 4)
    have e : (x 3 / x 4) ^ 2 + x 3 / x 4 + d = (x 3 ^ 2 + x 3 * x 4 + d * x 4 ^ 2) / x 4 ^ 2 := by
      field_simp
    rw [e, hnum, zero_div]
  have h3 : x 3 = 0 := by
    rw [h4] at hnum
    exact pow_eq_zero_iff two_ne_zero |>.1 (by linear_combination hnum)
  have h0 : x 0 = 0 := by rw [hx0', h3, h4]; ring
  have hxv : x ∈ (vStd' : HLine F).1 := mem_vStd'.2 ⟨h0, hx2, h3, h4, hx5⟩
  have hxQ : Qf x = 0 := hQx
  have hxL : x 0 + x 3 + d * x 4 = 0 := hL
  have := slineE_unique hd h2 hx0 hxQ hxL (s := ⟨w, hw'⟩) (s' := vS' d) hxw hxv
  exact congrArg Subtype.val this

/-- Distinct lines of `S_z` are opposite: no point of `v` is collinear with a point of `w`. -/
theorem slineZE_opp' [Fintype F] {d : F} (hd : ∀ t : F, t ^ 2 + t + d ≠ 0) (h2 : (2 : F) = 0) {z : F × F}
    (hz : z ≠ (0, 0)) {w : HLine F} (hw : ∀ x ∈ w.1, InPiZE d z.1 z.2 x) (hne : w ≠ vStd') :
    Opp (hexInc (F := F)) vStd' w := by
  rintro ⟨p, M, p', h1, h2', h3, h4⟩
  have hv : ∀ x ∈ (vStd' : HLine F).1, InPiZE d z.1 z.2 x := vStd'_PiZ d z.1 z.2
  have hp1 : InPiZE d z.1 z.2 p.1.rep := hv _ h1
  have hp1' : InPiZE d z.1 z.2 p'.1.rep := hw _ h4
  by_cases hpp : p = p'
  · subst hpp
    have := slineZE_unique (W := vStd') (W' := w) (α := z.1) (β := z.2) hd h2 p.1.rep_nonzero p.2
      hp1 hv hw h1 h4
    exact hne this.symm
  · have hMspan : M.1 = span F {p.1.rep, p'.1.rep} :=
      hline_eq_span M h2' h3 p.1.rep_nonzero (rep_not_mem_span_of_ne (fun h => hpp (Subtype.ext h)))
    have hMZ : ∀ x ∈ M.1, InPiZE d z.1 z.2 x := by
      intro x hx
      rw [hMspan] at hx
      obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hx
      unfold InPiZE at hp1 hp1' ⊢
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination a * hp1 + b * hp1'
    have e1 := slineZE_unique (W := vStd') (W' := M) (α := z.1) (β := z.2) hd h2 p.1.rep_nonzero p.2
      hp1 hv hMZ h1 h2'
    have e2 := slineZE_unique (W := w) (W' := M) (α := z.1) (β := z.2) hd h2 p'.1.rep_nonzero p'.2
      hp1' hw hMZ h4 h3
    exact hne (e2.trans e1.symm)

end BipartiteDD.HexagonEven
