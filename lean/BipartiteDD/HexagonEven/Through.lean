import BipartiteDD.HexagonEven.Plane
import BipartiteDD.Hexagon.Through

/-! Split Cayley hexagon `H(q)` for every finite field, part 2: every point lies on exactly `q + 1` lines.

Same double counting as `BipartiteDD.Hexagon.card_lines_through`, with `finrank_plane_all` (no `NeZero (2 : F)`).
The double-counting lemma `BipartiteDD.Hexagon.card_dc` is characteristic-free and is reused. -/

namespace BipartiteDD.HexagonEven

open BipartiteDD.Hexagon Module Submodule
open scoped Classical

variable {F : Type*} [Field F] [Fintype F]

theorem finite_hline_even : Finite (HLine F) :=
  Finite.of_injective (fun W : HLine F => (W.1 : Set (V7 F)))
    (fun a b h => Subtype.ext (SetLike.coe_injective h))

theorem card_lines_through_even (p : SPt F) :
    Nat.card {W : HLine F // p.1.rep ∈ W.1} = Fintype.card F + 1 := by
  set x := p.1.rep with hxdef
  have hx0 : x ≠ 0 := p.1.rep_nonzero
  have hQ : Qf x = 0 := p.2
  have hxplane : x ∈ plane x := mem_plane.2 (by rw [zmul_phi_self, hQ]; simp)
  have hq : 0 < Fintype.card F := Fintype.card_pos
  let S := {t : SPt F // t.1.rep ∈ plane x}
  let T := {W : HLine F // x ∈ W.1}
  haveI : Finite (HLine F) := finite_hline_even
  haveI : Finite T := Subtype.finite
  haveI : Fintype S := Fintype.ofFinite S
  haveI : Fintype T := Fintype.ofFinite T
  let p0 : S := ⟨p, hxplane⟩
  -- the number of points of the plane
  have hS : Fintype.card S = 1 + Fintype.card F + Fintype.card F ^ 2 := by
    have e : S ≃ {t : Projectivization F (V7 F) // t.rep ∈ plane x} :=
      { toFun := fun t => ⟨t.1.1, t.2⟩
        invFun := fun t => ⟨⟨t.1, Qf_eq_zero_of_mem_plane hx0 t.2⟩, t.2⟩
        left_inv := fun t => rfl
        right_inv := fun t => rfl }
    rw [← Nat.card_eq_fintype_card, Nat.card_congr e, card_points_mem,
      Projectivization.card_of_finrank F (plane x) (finrank_plane_all hx0 hQ)]
    simp [Finset.sum_range_succ, Nat.card_eq_fintype_card]
  -- every line through `x` has `q + 1` points of the plane
  have hT : ∀ W : T, (Finset.univ.filter (fun t : S => t.1.1.rep ∈ W.1.1)).card =
      Fintype.card F + 1 := by
    intro W
    have hWle := hline_le_plane W.1 hx0 W.2
    have e : {t : S // t.1.1.rep ∈ W.1.1} ≃ {t : SPt F // t.1.rep ∈ W.1.1} :=
      { toFun := fun t => ⟨t.1.1, t.2⟩
        invFun := fun t => ⟨⟨t.1, hWle t.2⟩, t.2⟩
        left_inv := fun t => rfl
        right_inv := fun t => rfl }
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, Nat.card_congr e, card_points_hline]
  -- every other point of the plane lies on exactly one line through `x`
  have hP : ∀ t : S, t ≠ p0 → (Finset.univ.filter (fun W : T => t.1.1.rep ∈ W.1.1)).card = 1 := by
    intro t htp
    have hnot : t.1.1.rep ∉ span F {x} := by
      intro hmem
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
      apply htp
      have h1 : t.1.1 = p.1 := by
        rw [← Projectivization.mk_rep t.1.1, ← Projectivization.mk_rep p.1,
          Projectivization.mk_eq_mk_iff']
        exact ⟨a, ha⟩
      exact Subtype.ext (Subtype.ext h1)
    have hpair : IsHPair x t.1.1.rep := (isHPair_iff_mem_plane hx0 hQ).2 t.2
    rw [Finset.card_eq_one]
    refine ⟨⟨hlineOf hx0 hpair hnot, subset_span (by simp)⟩, ?_⟩
    ext W
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hW
      apply Subtype.ext
      apply Subtype.ext
      exact hline_eq_span W.1 W.2 hW hx0 hnot
    · rintro rfl
      exact subset_span (by simp)
  have hmain := card_dc (S := S) (T := T) (fun t W => t.1.1.rep ∈ W.1.1) (Fintype.card F) hq p0
    hT hP (fun W => W.2) hS
  have e : {W : HLine F // p.1.rep ∈ W.1} ≃ T := Equiv.refl _
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  exact hmain

end BipartiteDD.HexagonEven
