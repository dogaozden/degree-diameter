import BipartiteDD.HexagonD.ChartB
import BipartiteDD.HexagonD.Delorme

/-! Theorem D, slice 2, part 15 (target 4, steps 2 and 4): the exact whisker set.

`vStd = ⟨e₁, e₆⟩` is the line `v` of the report, `Fz` the function `F(z) = G(z)/(α² + cβ²)` and
`Wset c c0 c1` the set of lines `m ∈ S_z ∖ {v}`, `z ≠ 0`, whose point in `Π` has `ν = F(z)`.

* `exact_of_family`: abstract form of steps 2-4. If, for a normalised free vector `u` (`Q u = 0`, `L u = 1`), the
  points `X s` of the `S_{z(s)}`-lines through `u` (all `z(s)` with `u ∈ Π_z`) have a unique `s` with
  `ν(X s) = F(z(s))`, then `u` is on exactly one line of `Wset`.
* `no_second_line`: a line of `S_z` (`z ≠ 0`) inside `Π` is `v`. -/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace BipartiteDD.HexagonD

open BipartiteDD.Hexagon Module Submodule

variable {F : Type*} [Field F] [Fintype F] [NeZero (2 : F)] {c : F}

/-- A nonzero vector of a line in the kernel of a linear form. -/
theorem exists_ker_vec (w : HLine F) (f : V7 F →ₗ[F] F) : ∃ x ∈ w.1, x ≠ 0 ∧ f x = 0 := by
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

/-! ### The line `v = ⟨e₁, e₆⟩` -/

theorem e1_ne : (Pi.single 1 1 : V7 F) ≠ 0 := by
  intro h
  have := congr_fun h 1
  simp at this

theorem e1e6_pair : IsHPair (Pi.single 1 1 : V7 F) (Pi.single 6 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Qf, Bf, Tits, pl, Pi.single_apply]

theorem e6_not_mem : (Pi.single 6 1 : V7 F) ∉ span F {(Pi.single 1 1 : V7 F)} := by
  intro h
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 h
  have := congr_fun ha 6
  simp at this

/-- The line `v = ⟨e₁, e₆⟩` of the report. -/
def vStd : HLine F := hlineOf e1_ne e1e6_pair e6_not_mem

theorem mem_vStd {x : V7 F} : x ∈ (vStd : HLine F).1 ↔
    x 0 = 0 ∧ x 2 = 0 ∧ x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0 := by
  constructor
  · intro hx
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hx
    simp [Pi.single_apply]
  · rintro ⟨h0, h2, h3, h4, h5⟩
    refine Submodule.mem_span_pair.2 ⟨x 1, x 6, ?_⟩
    ext i
    fin_cases i <;> simp [Pi.single_apply, *]

theorem vStd_Lz (c α β : F) : InPiZ c α β (vStd : HLine F) := by
  intro x hx
  obtain ⟨h0, h2, h3, h4, h5⟩ := mem_vStd.1 hx
  simp [Lz, *]

theorem vStd_inPi (c : F) : InPi c (vStd : HLine F) := by
  intro x hx
  obtain ⟨h0, h2, h3, h4, h5⟩ := mem_vStd.1 hx
  simp [*]

/-- The spread line `v`. -/
def vS (c : F) : SLine c := ⟨vStd, vStd_inPi c⟩

/-! ### The whisker set -/

/-- `F(z) = G(z)/(α² + cβ²)` with `G(a, b) = (c₀ a + c₁ b)(a² + c b²) - b³`. -/
def Fz (c c0 c1 : F) (z : F × F) : F :=
  ((c0 * z.1 + c1 * z.2) * (z.1 ^ 2 + c * z.2 ^ 2) - z.2 ^ 3) / (z.1 ^ 2 + c * z.2 ^ 2)

/-- The exact whisker set of Theorem 4. -/
def Wset (c c0 c1 : F) : Set (HLine F) :=
  {m | m ≠ vStd ∧ ∃ z : F × F, z ≠ (0, 0) ∧ InPiZ c z.1 z.2 m ∧
    ∃ x ∈ m.1, x ≠ 0 ∧ x 0 + c * x 4 = 0 ∧ nuf c x = Fz c c0 c1 z}

theorem alpha_beta_ne {c : F} (hc : ¬ IsSquare (-c)) {z : F × F} (hz : z ≠ (0, 0)) :
    z.1 ^ 2 + c * z.2 ^ 2 ≠ 0 := by
  have : z.1 ^ 2 + c * z.2 ^ 2 = c * z.2 ^ 2 + z.1 ^ 2 := by ring
  rw [this]
  refine aniso_ne hc (fun h => hz (Prod.ext h.2 h.1))

/-- A line of `S_z` (`z ≠ 0`) lying in `Π` is `v`. -/
theorem no_second_line (hc : ¬ IsSquare (-c)) {z : F × F} (hz : z ≠ (0, 0)) {w : HLine F}
    (hw : InPiZ c z.1 z.2 w) (hw' : InPi c w) : w = vStd := by
  have hD := alpha_beta_ne hc hz
  let f : V7 F →ₗ[F] F := (c * z.2) • LinearMap.proj 2 - z.1 • LinearMap.proj 5
  obtain ⟨x, hxw, hx0, hfx⟩ := exists_ker_vec w f
  have hfx' : c * z.2 * x 2 - z.1 * x 5 = 0 := by simpa [f] using hfx
  have hL : x 0 + c * x 4 = 0 := hw' x hxw
  have hLz : x 0 + c * x 4 + z.1 * x 2 + z.2 * x 5 = 0 := hw x hxw
  have hx2 : x 2 = 0 := by
    have : (z.1 ^ 2 + c * z.2 ^ 2) * x 2 = 0 := by
      linear_combination z.1 * (hLz - hL) + z.2 * hfx'
    exact (mul_eq_zero.1 this).resolve_left hD
  have hx5 : x 5 = 0 := by
    have : (z.1 ^ 2 + c * z.2 ^ 2) * x 5 = 0 := by
      linear_combination c * z.2 * (hLz - hL) - z.1 * hfx'
    exact (mul_eq_zero.1 this).resolve_left hD
  have hQ : Qf x = 0 := Qf_eq_zero_of_mem_hline w hxw
  have hx0' : x 0 = -(c * x 4) := by linear_combination hL
  have h34 : c * x 4 ^ 2 + x 3 ^ 2 = 0 := by
    simp only [Qf] at hQ
    rw [hx0', hx2, hx5] at hQ
    linear_combination -hQ
  obtain ⟨hx4, hx3⟩ := aniso hc h34
  have hxv : x ∈ (vStd : HLine F).1 :=
    mem_vStd.2 ⟨by rw [hx0', hx4]; ring, hx2, hx3, hx4, hx5⟩
  exact slineZ_unique hc z.1 z.2 hx0 hQ hLz hw (vStd_Lz c z.1 z.2) hxw hxv

end BipartiteDD.HexagonD
