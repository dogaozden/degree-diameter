import BipartiteDD.Plus2.Main

/-! Group F: a frame exists as soon as the order is at least 4, so the `+2` theorem holds for
every finite projective plane of order `q ≥ 4`. -/

namespace BipartiteDD.Plus2
open Configuration

/-- The index of each row among the five chosen points of a line: `P0 ↦ 0`, `X s ↦ idx s`. -/
def rowIdx : Row → Fin 5
  | .r0 => 1
  | .r1 => 2
  | .ra => 3
  | .rc => 4

theorem rowIdx_inj : Function.Injective rowIdx := by decide

theorem rowIdx_ne_zero : ∀ s : Row, rowIdx s ≠ 0 := by decide

/-- Every frame needs a line with five points, and a point off it. -/
theorem Frame.exists {P L : Type*} [Membership P L] [ProjectivePlane P L] [Fintype P]
    [Fintype L] (h : 4 ≤ ProjectivePlane.order P L) : Nonempty (Frame P L) := by
  classical
  obtain ⟨-, -, -, ℓ, -, -, -⟩ := ProjectivePlane.exists_config (P := P) (L := L)
  obtain ⟨A, hA⟩ := Nondegenerate.exists_point (P := P) (L := L) ℓ
  have hcard : Fintype.card {p : P // p ∈ ℓ} = ProjectivePlane.order P L + 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact ProjectivePlane.pointCount_eq (P := P) (L := L) ℓ
  have hle : Fintype.card (Fin 5) ≤ Fintype.card {p : P // p ∈ ℓ} := by
    rw [hcard, Fintype.card_fin]
    omega
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hle
  have hX_inj : Function.Injective (fun s : Row => (f (rowIdx s)).1) := by
    intro s t hst
    have := f.injective (Subtype.ext hst)
    exact rowIdx_inj this
  have hX_ne : ∀ s : Row, (fun s : Row => (f (rowIdx s)).1) s ≠ (f 0).1 := by
    intro s hst
    have := f.injective (Subtype.ext hst)
    exact rowIdx_ne_zero s this
  exact ⟨⟨ℓ, A, (f 0).1, fun s => (f (rowIdx s)).1, hA, (f 0).2,
    fun s => (f (rowIdx s)).2, hX_inj, hX_ne⟩⟩

/-- The `+2` theorem for every projective plane of order at least `4`. -/
theorem plus2_of_order {P L : Type*} [Membership P L] [ProjectivePlane P L] [Fintype P]
    [Fintype L] (h : 4 ≤ ProjectivePlane.order P L) :
    ∃ G : SimpleGraph (Fin (2 * (ProjectivePlane.order P L ^ 2 + ProjectivePlane.order P L + 6))),
      IsBipartiteDegDiam G (ProjectivePlane.order P L + 2) 3 := by
  obtain ⟨F⟩ := Frame.exists h
  exact plus2 F

end BipartiteDD.Plus2
