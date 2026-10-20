import BipartiteDD.Hexagon.Plane

/-! Split Cayley hexagon `H(q)`, part 4: the lines.

`isHPair_iff`: the pair `(x, y)` satisfies the Tits predicate `IsHPair` iff both are singular and the octonion
product `φ x · φ y` vanishes. Consequently lines of `H(q)` through a nonzero singular `x` are exactly the
2-dimensional subspaces `⟨x, y⟩` with `y ∈ π_x` (`plane x`). -/

namespace BipartiteDD.Hexagon

open Module

variable {F : Type*} [Field F]

theorem zmul_phi_e3 (x : V7 F) :
    zmul (phi x) (phi (Pi.single 3 1 : V7 F)) = ![x 3, x 3, x 0, x 1, x 2, x 4, x 5, x 6] := by
  ext k
  fin_cases k <;> simp [zmul, phi]

theorem isHPair_iff {x y : V7 F} :
    IsHPair x y ↔ Qf x = 0 ∧ Qf y = 0 ∧ zmul (phi x) (phi y) = 0 := by
  constructor
  · rintro ⟨hx, hy, hB, t1, t2, t3, t4, t5, t6⟩
    refine ⟨hx, hy, ?_⟩
    by_cases hx0 : x = 0
    · subst hx0; rw [phi_zero, zmul_zero_left]
    set P := zmul (phi x) (phi y) with hPdef
    simp only [pl] at t1 t2 t3 t4 t5 t6
    have hP : P = P 0 • phi (Pi.single 3 1 : V7 F) := by
      ext k
      fin_cases k <;> simp [hPdef, zmul, phi, Pi.single_apply]
      · simp only [Bf] at hB
        linear_combination -hB
      · linear_combination t4
      · linear_combination t6
      · linear_combination t2
      · linear_combination t1
      · linear_combination t3
      · linear_combination t5
    have h1 := zmul_alt_left (phi x) (phi y)
    rw [zmul_phi_self, hx, neg_zero, zero_smul, zmul_zero_left] at h1
    rw [← hPdef, hP, zmul_smul_right, zmul_phi_e3] at h1
    by_contra hne
    have hP0 : P 0 ≠ 0 := by
      intro h0
      apply hne
      rw [hP, h0, zero_smul]
    apply hx0
    have hs : ∀ j, ![x 3, x 3, x 0, x 1, x 2, x 4, x 5, x 6] j = 0 := fun j => by
      have := congr_fun h1 j
      rw [Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at this
      exact (mul_eq_zero.1 this).resolve_left hP0
    have e0 := hs 2
    have e1 := hs 3
    have e2 := hs 4
    have e3 := hs 0
    have e4 := hs 5
    have e5 := hs 6
    have e6 := hs 7
    simp at e0 e1 e2 e3 e4 e5 e6
    ext i
    fin_cases i <;> simp [*]
  · rintro ⟨hx, hy, hP⟩
    have e : ∀ k, zmul (phi x) (phi y) k = 0 := fun k => by rw [hP]; rfl
    have e0 := e 0
    have e1 := e 1
    have e2 := e 2
    have e3 := e 3
    have e4 := e 4
    have e5 := e 5
    have e6 := e 6
    have e7 := e 7
    simp [zmul, phi] at e0 e1 e2 e3 e4 e5 e6 e7
    refine ⟨hx, hy, ?_, ?_⟩
    · simp only [Bf]; linear_combination -(e0 + e1)
    · simp only [Tits, pl]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · linear_combination e5
      · linear_combination e4
      · linear_combination e6
      · linear_combination e2
      · linear_combination e7
      · linear_combination e3

theorem isHPair_iff_mem_plane {x y : V7 F} (hx : x ≠ 0) (hQ : Qf x = 0) :
    IsHPair x y ↔ y ∈ plane x := by
  rw [isHPair_iff, mem_plane]
  refine ⟨fun h => h.2.2, fun h => ⟨hQ, Qf_eq_zero_of_mem_plane hx (mem_plane.2 h), h⟩⟩

end BipartiteDD.Hexagon
