import BipartiteDD.Plus2Zero.Diam

/-! A frame exists as soon as the order is at least `3`: a line has `q + 1 ≥ 4` points, and a
point off it exists, so the four feet `X h` can be chosen. -/

namespace BipartiteDD.Plus2Zero
open Configuration

/-- Every projective plane of order at least `3` carries a frame. -/
theorem Frame.exists {P L : Type*} [Membership P L] [ProjectivePlane P L] [Fintype P]
    [Fintype L] (h : 3 ≤ ProjectivePlane.order P L) : Nonempty (Frame P L) := by
  classical
  obtain ⟨-, -, -, ℓ, -, -, -⟩ := ProjectivePlane.exists_config (P := P) (L := L)
  obtain ⟨A, hA⟩ := Nondegenerate.exists_point (P := P) (L := L) ℓ
  have hcard : Fintype.card {p : P // p ∈ ℓ} = ProjectivePlane.order P L + 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact ProjectivePlane.pointCount_eq (P := P) (L := L) ℓ
  have hle : Fintype.card Hat ≤ Fintype.card {p : P // p ∈ ℓ} := by
    have h4 : Fintype.card Hat = 4 := rfl
    rw [hcard, h4]
    omega
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hle
  refine ⟨⟨ℓ, A, fun k => (f k).1, hA, fun k => (f k).2, ?_⟩⟩
  intro i j hij
  exact f.injective (Subtype.ext hij)

end BipartiteDD.Plus2Zero
