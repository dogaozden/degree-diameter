import BipartiteDD.Haar.LiftC.Cover

/-! The covering hypothesis of the (5,10) record, in `Z_1989 ⋊ Z_24`.

`CoverHyp` is the hypothesis of `haar_isBipartiteDegDiam10_of_equiv` (the nine-letter condition of `Diam10`), written
as a definition with the group operations of the `Group` instance. The word `wordG c` is `wordOf` at the letters of
the code `c`, so `cover : CoverHyp SS` is proved by unfolding, and the record passes `cover` directly. This is the
fix of `research/lean-haarD/STATUS-d6D10c.md` (a cover written through the direct instances of a concrete product group
times out at `isDefEq` under the `∃` binders). -/

namespace BipartiteDD.Haar.LiftC

open BipartiteDD.Haar.LiftC.Meta1989

/-- The nine-letter covering condition of `haar_isBipartiteDegDiam10_of_equiv`, for a general group. -/
def CoverHyp {G : Type*} [Group G] (S : Finset G) : Prop :=
  ∀ g : G, ∃ x₁ ∈ S, ∃ x₂ ∈ S, ∃ x₃ ∈ S, ∃ x₄ ∈ S, ∃ x₅ ∈ S, ∃ x₆ ∈ S, ∃ x₇ ∈ S, ∃ x₈ ∈ S,
    ∃ x₉ ∈ S, g = x₁ * (x₂⁻¹ * (x₃ * (x₄⁻¹ * (x₅ * (x₆⁻¹ * (x₇ * (x₈⁻¹ * x₉)))))))

theorem cover : CoverHyp SS := by
  unfold CoverHyp
  intro g
  obtain ⟨c, hc⟩ := exC (enc g) (enc_lt g)
  refine ⟨sel (dig c 0), sel_mem _ (dig_lt c 0), sel (dig c 1), sel_mem _ (dig_lt c 1),
    sel (dig c 2), sel_mem _ (dig_lt c 2), sel (dig c 3), sel_mem _ (dig_lt c 3),
    sel (dig c 4), sel_mem _ (dig_lt c 4), sel (dig c 5), sel_mem _ (dig_lt c 5),
    sel (dig c 6), sel_mem _ (dig_lt c 6), sel (dig c 7), sel_mem _ (dig_lt c 7),
    sel (dig c 8), sel_mem _ (dig_lt c 8), ?_⟩
  exact (grpOf_enc g).symm.trans (okC_spec hc)

end BipartiteDD.Haar.LiftC
