import BipartiteDD.LeanMaxx.D5.Layout7
import BipartiteDD.SingerC.W3Main

/-! # D = 5 formalisation, part 10: a family for every odd `q` (Corollary 10.3, formal form)

`W(3, q)` on the Singer setting (`BipartiteDD.SingerC`, one `Setting` per odd prime power `q`) is a generalized
quadrangle of order `(q, q)` with the regular spread of `q² + 1` pairwise disjoint lines. A maximal set of pairwise
non-collinear points ("partial ovoid") has at least `q - 1` points by counting (`exists_partial_ovoid`). Feeding the
spread and such a set to `layout7` gives, for **every odd prime power `q`** and every `1 ≤ K ≤ q - 3`, a bipartite
graph of maximum degree `q + 4` and diameter `≤ 5` with `14 (q + 1)(q² + 1) + 2K` vertices (`family_odd`).

This is the shape of Corollary 10.3 of `research/theorems/D5_QUADRANGLE.md` with the explicit partial ovoid of
Lemma 1.3 replaced by the counting bound, the non-friendly arcs left whole (`c = 0`) and the complete bipartite
hub graph (Y0); the numbers are therefore smaller than the note's (`K ≤ 6q`, `K_𝓐 ≤ 3q + 3`, `c = 2`). -/

namespace BipartiteDD.LeanMaxx.D5

open SimpleGraph BipartiteDD Finset
open scoped Classical

set_option linter.unusedSectionVars false

section Ovoid

variable {P L : Type*} [Membership P L] [Fintype P] [Fintype L] {q : ℕ}

theorem card_lines_through (G : GQst P L q q) (p : P) : (univ.filter (fun l : L => p ∈ l)).card = q + 1 := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact G.lines_on_pt p

theorem card_pts_on (G : GQst P L q q) (l : L) : (univ.filter (fun p : P => p ∈ l)).card = q + 1 := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact G.pts_on_line l

/-- A maximal partial ovoid dominates all points: `|P| ≤ |Z| (q + 1)²`. -/
theorem exists_partial_ovoid (G : GQst P L q q) :
    ∃ Z : Finset P, (∀ p ∈ Z, ∀ p' ∈ Z, p ≠ p' → ¬ Co (.inl p : P ⊕ L) (.inl p')) ∧
      Fintype.card P ≤ Z.card * ((q + 1) * (q + 1)) := by
  let 𝒵 : Finset (Finset P) :=
    univ.filter (fun Z => ∀ p ∈ Z, ∀ p' ∈ Z, p ≠ p' → ¬ Co (.inl p : P ⊕ L) (.inl p'))
  have h0 : (∅ : Finset P) ∈ 𝒵 := by simp [𝒵]
  obtain ⟨Z, hZ𝒵, hZmax⟩ := Finset.exists_max_image 𝒵 Finset.card ⟨∅, h0⟩
  have hZ : ∀ p ∈ Z, ∀ p' ∈ Z, p ≠ p' → ¬ Co (.inl p : P ⊕ L) (.inl p') := by
    simpa [𝒵] using hZ𝒵
  refine ⟨Z, hZ, ?_⟩
  have hcover : ∀ p : P, p ∈ Z ∨ ∃ z ∈ Z, Co (.inl p : P ⊕ L) (.inl z) := by
    intro p
    by_cases hp : p ∈ Z
    · exact Or.inl hp
    right
    by_contra hcon
    push_neg at hcon
    have hmem : insert p Z ∈ 𝒵 := by
      simp only [𝒵, mem_filter, mem_univ, true_and]
      intro a ha b hb hab
      rw [mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact absurd rfl hab
      · exact hcon b hb
      · intro hco; exact hcon a ha hco.symm
      · exact hZ a ha b hb hab
    have := hZmax _ hmem
    rw [card_insert_of_notMem hp] at this
    omega
  let N : P → Finset P := fun z => (univ.filter (fun l : L => z ∈ l)).biUnion (fun l => univ.filter (fun p : P => p ∈ l))
  have hsub : (univ : Finset P) ⊆ Z.biUnion N := by
    intro p _
    rcases hcover p with hp | ⟨z, hz, hco⟩
    · obtain ⟨l, hl⟩ := G.exists_line p
      exact mem_biUnion.2 ⟨p, hp, mem_biUnion.2 ⟨l, by simpa using hl, by simpa using hl⟩⟩
    · obtain ⟨-, c, hc1, hc2⟩ := hco
      rcases c with c | l
      · exact absurd hc1 incGraph_not_adj_inl_inl
      · exact mem_biUnion.2 ⟨z, hz, mem_biUnion.2 ⟨l, by simpa using incGraph_adj_inr_inl.1 hc2,
          by simpa using incGraph_adj_inl_inr.1 hc1⟩⟩
  have hN : ∀ z, (N z).card ≤ (q + 1) * (q + 1) := by
    intro z
    refine (card_biUnion_le).trans (le_of_eq ?_)
    calc ∑ l ∈ univ.filter (fun l : L => z ∈ l), (univ.filter (fun p : P => p ∈ l)).card
        = ∑ l ∈ univ.filter (fun l : L => z ∈ l), (q + 1) := sum_congr rfl (fun l _ => card_pts_on G l)
      _ = (q + 1) * (q + 1) := by rw [sum_const, card_lines_through G, smul_eq_mul]
  calc Fintype.card P = (univ : Finset P).card := (card_univ).symm
    _ ≤ (Z.biUnion N).card := card_le_card hsub
    _ ≤ ∑ z ∈ Z, (N z).card := card_biUnion_le
    _ ≤ ∑ z ∈ Z, ((q + 1) * (q + 1)) := sum_le_sum (fun z _ => hN z)
    _ = Z.card * ((q + 1) * (q + 1)) := by rw [sum_const, smul_eq_mul]

end Ovoid

end BipartiteDD.LeanMaxx.D5

namespace BipartiteDD.SingerC.Setting

open BipartiteDD BipartiteDD.LeanMaxx.D5 SimpleGraph Finset
open scoped LinearAlgebra.Projectivization Classical

variable {K : Type*} [Field K] [Fintype K] {p : ℕ} [Fact p.Prime] [CharP K p] (S : Setting K p)

/-- **Corollary 10.3, formal form, for every odd prime power `q`.** For `q = S.q` and `1 ≤ k ≤ q - 3` there is a
bipartite graph of maximum degree `q + 4` and diameter at most `5` with `14 (q + 1)(q² + 1) + 2k` vertices:
seven levels `HHHDHHD` over `W(3, q)` with the regular spread freed on the `H → D` arcs, a maximal partial ovoid
on the `D → H` arcs, `k` hubs of each kind and a complete bipartite hub graph. -/
theorem family_odd {k : ℕ} (hk1 : 1 ≤ k) (hkq : k + 3 ≤ S.q) :
    ∃ Y : SimpleGraph (Fin (14 * ((S.q + 1) * (S.q ^ 2 + 1)) + k + k)),
      IsBipartiteDegDiam Y (S.q + 1 + 3) 5 := by
  have G := S.gq_W
  have hP : Fintype.card (ℙ S.F K) = (S.q + 1) * (S.q ^ 2 + 1) := by
    rw [← Nat.card_eq_fintype_card, S.card_points]
  have hL : Fintype.card S.TILine = (S.q + 1) * (S.q ^ 2 + 1) := by
    rw [← Nat.card_eq_fintype_card, S.card_lines]
  let e : ℙ S.F K ≃ S.TILine := Fintype.equivOfCardEq (hP.trans hL.symm)
  let Sp : Finset S.TILine := univ.filter (fun l => S.IsSpread l)
  have hSp : Sp.card = S.q ^ 2 + 1 := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact S.card_spread
  have hdisj : ∀ l ∈ Sp, ∀ l' ∈ Sp, l ≠ l' → ¬ Co (.inr l : ℙ S.F K ⊕ S.TILine) (.inr l') := by
    intro l hl l' hl' hne hco
    simp only [Sp, mem_filter, mem_univ, true_and] at hl hl'
    obtain ⟨-, c, hc1, hc2⟩ := hco
    rcases c with x | m
    · exact hne (S.spread_unique hl hl' (incGraph_adj_inr_inl.1 hc1) (incGraph_adj_inl_inr.1 hc2))
    · exact absurd hc1 incGraph_not_adj_inr_inr
  obtain ⟨Z, hZ, hZcard⟩ := exists_partial_ovoid G
  have hZ' : S.q - 1 ≤ Z.card := by
    rw [hP] at hZcard
    by_contra hcon
    push_neg at hcon
    have h1 : Z.card + 2 ≤ S.q := by omega
    have h2 : (S.q + 1) * (S.q ^ 2 + 1) ≤ Z.card * ((S.q + 1) * (S.q + 1)) := hZcard
    have h3 : S.q ^ 2 + 1 ≤ Z.card * (S.q + 1) := by
      have : (S.q + 1) * (S.q ^ 2 + 1) ≤ (S.q + 1) * (Z.card * (S.q + 1)) := by nlinarith
      exact Nat.le_of_mul_le_mul_left this (Nat.succ_pos _)
    nlinarith
  obtain ⟨Y, hY⟩ := layout7 (K := k) G e Sp Z hdisj hZ hk1 (by rw [hSp]; nlinarith) (by omega) hkq
  have : 7 * (Fintype.card (ℙ S.F K) + Fintype.card S.TILine) + k + k =
      14 * ((S.q + 1) * (S.q ^ 2 + 1)) + k + k := by rw [hP, hL]; ring
  rw [← this]
  exact ⟨Y, hY⟩

end BipartiteDD.SingerC.Setting
