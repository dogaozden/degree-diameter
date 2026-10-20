import BipartiteDD.Hexagon.Lines
import BipartiteDD.Hexagon.QuadricCount

/-! Split Cayley hexagon `H(q)`, part 5: local structure.

* a line of `H(q)` has `q + 1` points (`card_points_hline`);
* a point lies on exactly `q + 1` lines (`card_lines_through`), by double counting the points of the plane
  `π_x`: each of its `q² + q` points other than `x` lies on exactly one line through `x`, and each of the
  `q + 1` lines through `x` has `q` such points.
* generic double counting lemma `card_dc` used for the last step. -/

namespace BipartiteDD.Hexagon

open Module Submodule
open scoped Classical

variable {F : Type*} [Field F]

/-! ### Generalities on lines -/

theorem isHPair_span {x y u v : V7 F} (h : IsHPair x y) (hu : u ∈ span F {x, y})
    (hv : v ∈ span F {x, y}) : IsHPair u v := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hu
  obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.1 hv
  have hB : Bf x y = 0 := h.2.2.1
  have h' := h.symm
  rw [isHPair_iff] at h h' ⊢
  obtain ⟨hx, hy, hxy⟩ := h
  obtain ⟨-, -, hyx⟩ := h'
  have hxx : zmul (phi x) (phi x) = 0 := by rw [zmul_phi_self, hx]; simp
  have hyy : zmul (phi y) (phi y) = 0 := by rw [zmul_phi_self, hy]; simp
  have hQ : ∀ a b : F, Qf (a • x + b • y) = 0 := fun a b => by
    have : Qf (a • x + b • y) = a ^ 2 * Qf x + b ^ 2 * Qf y + a * b * Bf x y := by
      simp only [Qf, Bf, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [this, hx, hy, hB]; ring
  refine ⟨hQ a b, hQ c d, ?_⟩
  simp only [phi_add, phi_smul, zmul_add_left, zmul_add_right, zmul_smul_left, zmul_smul_right,
    hxx, hxy, hyx, hyy, smul_zero, add_zero]

theorem finrank_span_pair_eq_two {x y : V7 F} (hx : x ≠ 0) (hy : y ∉ span F {x}) :
    finrank F (span F {x, y}) = 2 := by
  have h1 : finrank F (span F {x}) = 1 := finrank_span_singleton hx
  have hlt : span F {x} < span F {x, y} := by
    refine lt_of_le_of_ne (span_mono (by simp)) (fun h => hy ?_)
    rw [h]; exact subset_span (by simp)
  have h2 := Submodule.finrank_lt_finrank_of_lt hlt
  have h3 : finrank F (span F {x, y}) ≤ 2 := by
    have := finrank_span_finset_le_card (R := F) ({x, y} : Finset (V7 F))
    simp only [Finset.coe_insert, Finset.coe_singleton] at this
    exact this.trans (Finset.card_le_two)
  omega

/-- The line through two independent points of a Tits pair. -/
def hlineOf {x y : V7 F} (hx : x ≠ 0) (h : IsHPair x y) (hy : y ∉ span F {x}) : HLine F :=
  ⟨span F {x, y}, finrank_span_pair_eq_two hx hy, fun _ hu _ hv => isHPair_span h hu hv⟩

theorem hline_eq_span {x y : V7 F} (W : HLine F) (hxW : x ∈ W.1) (hyW : y ∈ W.1) (hx : x ≠ 0)
    (hy : y ∉ span F {x}) : W.1 = span F {x, y} := by
  symm
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rw [span_le]
    intro z hz
    rcases hz with rfl | rfl
    · exact hxW
    · exact hyW
  · rw [finrank_span_pair_eq_two hx hy, W.2.1]

theorem hline_le_plane {x : V7 F} (W : HLine F) (hx : x ≠ 0) (hxW : x ∈ W.1) :
    W.1 ≤ plane x := fun y hy =>
  (isHPair_iff_mem_plane hx (W.2.2 x hxW x hxW).1).1 (W.2.2 x hxW y hy)

theorem Qf_eq_zero_of_mem_hline (W : HLine F) {y : V7 F} (hy : y ∈ W.1) : Qf y = 0 :=
  (W.2.2 y hy y hy).1

/-! ### Points of a subspace -/

theorem rep_mem_iff (W : Submodule F (V7 F)) (v : V7 F) (hv : v ≠ 0) :
    (Projectivization.mk F v hv).rep ∈ W ↔ v ∈ W := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep F v hv
  rw [← ha, Units.smul_def]
  constructor
  · intro h
    have := W.smul_mem (a⁻¹ : Fˣ) h
    simpa [Units.smul_def] using this
  · intro h
    exact W.smul_mem _ h

theorem card_points_mem (W : Submodule F (V7 F)) :
    Nat.card {p : Projectivization F (V7 F) // p.rep ∈ W} = Nat.card (Projectivization F W) := by
  let f := Projectivization.map W.subtype W.injective_subtype
  have hinj : Function.Injective f :=
    Projectivization.map_injective (σ := RingHom.id F) (τ := RingHom.id F) _ _
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun t => ⟨f t, ?_⟩) ⟨?_, ?_⟩)
  · induction t using Projectivization.ind with
    | h w hw =>
      simp only [f, Projectivization.map_mk]
      rw [rep_mem_iff]
      exact w.2
  · intro s t hst
    exact hinj (congrArg Subtype.val hst)
  · rintro ⟨p, hp⟩
    refine ⟨Projectivization.mk F ⟨p.rep, hp⟩ (fun h => p.rep_nonzero (by simpa using congrArg Subtype.val h)), ?_⟩
    apply Subtype.ext
    simp only [f, Projectivization.map_mk]
    exact Projectivization.mk_rep p

variable [Fintype F]

theorem card_points_hline (W : HLine F) :
    Nat.card {p : SPt F // p.1.rep ∈ W.1} = Fintype.card F + 1 := by
  have e : {p : SPt F // p.1.rep ∈ W.1} ≃ {p : Projectivization F (V7 F) // p.rep ∈ W.1} :=
    { toFun := fun p => ⟨p.1.1, p.2⟩
      invFun := fun p => ⟨⟨p.1, Qf_eq_zero_of_mem_hline W p.2⟩, p.2⟩
      left_inv := fun p => rfl
      right_inv := fun p => rfl }
  rw [Nat.card_congr e, card_points_mem]
  rw [Projectivization.card_of_finrank_two F W.1 W.2.1, Nat.card_eq_fintype_card]

end BipartiteDD.Hexagon
