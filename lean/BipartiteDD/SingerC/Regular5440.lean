import BipartiteDD.SingerC.W3Main
import BipartiteDD.GQST.Regular
import Mathlib.FieldTheory.Finite.GaloisField

/-! Step 3 of the lean-regular4 brief: a 16-regular bipartite graph of diameter at most 4 on 5440
vertices. It is the copy graph of `W(3,13)` (the GQ of order `(13, 13)`) with the Singer 2-ovoid `O`
given weight `1` on each point of `O`, and the regular spread given weight `2` on each spread line.
Every line meets `O` in two points, and every point lies on exactly one spread line, so both weight
conditions are exact. `GQST.regular_copy_graph_fin` then gives the regular graph. -/

namespace BipartiteDD.SingerC

open Finset
open scoped LinearAlgebra.Projectivization

namespace Setting

variable {K : Type*} [Field K] [Fintype K] {p : ℕ} [Fact p.Prime] [CharP K p]

open Classical in
/-- Every point of `W(3,q)` lies on exactly one spread line. -/
theorem card_spread_through (S : Setting K p) (x : ℙ S.F K) :
    (univ.filter (fun l : S.TILine => x ∈ l ∧ S.IsSpread l)).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨S.spreadLine x.rep_nonzero, ?_⟩
  ext l
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, hsp⟩
    exact S.spread_unique hsp ⟨x.rep, x.rep_nonzero, rfl⟩ hx (S.pt_mem_spreadLine x)
  · rintro rfl
    exact ⟨S.pt_mem_spreadLine x, ⟨x.rep, x.rep_nonzero, rfl⟩⟩

/-- The regular copy graph of `W(3,q)`, for any Singer setting, of degree `q + 3` on
`2 (q² + 1)(q + 3)` vertices. -/
theorem regular_W3 (S : Setting K p) :
    ∃ H : SimpleGraph (Fin (2 * (S.q ^ 2 + 1) * (S.q + 3))),
      H.Colorable 2 ∧ (∀ v, (H.neighborSet v).ncard = S.q + 3) ∧ H.ediam ≤ 4 := by
  classical
  let w : ℙ S.F K → ℕ := fun x => if S.Oz 0 x.rep then 1 else 0
  let m : S.TILine → ℕ := fun l => if S.IsSpread l then 2 else 0
  have hw : ∀ l : S.TILine, ∑ x ∈ Finset.univ.filter (fun x => x ∈ l), w x = S.q + 3 - (S.q + 1) := by
    intro l
    have hc : ((Finset.univ.filter (fun x => x ∈ l)).filter (fun x => S.Oz 0 x.rep)).card = 2 := by
      have h := S.card_O_line (Nat.zero_le _) l
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
      rw [Finset.filter_filter]
      convert h using 2
    have hs : ∑ x ∈ Finset.univ.filter (fun x => x ∈ l), w x =
        ((Finset.univ.filter (fun x => x ∈ l)).filter (fun x => S.Oz 0 x.rep)).card := by
      simp only [w, Finset.sum_boole, Nat.cast_id]
    rw [hs, hc]
    omega
  have hm : ∀ x : ℙ S.F K, ∑ l ∈ Finset.univ.filter (fun l : S.TILine => x ∈ l), m l =
      S.q + 3 - (S.q + 1) := by
    intro x
    have hs : ∑ l ∈ Finset.univ.filter (fun l : S.TILine => x ∈ l), m l =
        ∑ l ∈ Finset.univ.filter (fun l : S.TILine => x ∈ l ∧ S.IsSpread l), 2 := by
      rw [Finset.sum_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases h1 : x ∈ l <;> by_cases h2 : S.IsSpread l <;> simp [m, h1, h2]
    rw [hs, Finset.sum_const, smul_eq_mul, S.card_spread_through x]
    omega
  have hP : Fintype.card (ℙ S.F K) = (S.q + 1) * (S.q ^ 2 + 1) := by
    rw [← Nat.card_eq_fintype_card, S.card_points]
  have hL : Fintype.card S.TILine = (S.q + 1) * (S.q ^ 2 + 1) := by
    rw [← Nat.card_eq_fintype_card, S.card_lines]
  have hW : ∑ x, w x = 2 * (S.q ^ 2 + 1) := by
    have hc : (Finset.univ.filter (fun x : ℙ S.F K => S.Oz 0 x.rep)).card = 2 * (S.q ^ 2 + 1) := by
      have h := S.card_O (Nat.zero_le _)
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
      exact h
    simp only [w, Finset.sum_boole, Nat.cast_id]
    exact hc
  have hM : ∑ l, m l = 2 * (S.q ^ 2 + 1) := by
    have hc : (Finset.univ.filter (fun l : S.TILine => S.IsSpread l)).card = S.q ^ 2 + 1 := by
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      exact S.card_spread
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, hc, mul_comm]
  have hn : Fintype.card (ℙ S.F K) + Fintype.card S.TILine + ∑ x, w x + ∑ l, m l =
      2 * (S.q ^ 2 + 1) * (S.q + 3) := by
    rw [hP, hL, hW, hM]
    ring
  obtain ⟨H, hc, hd, he⟩ := BipartiteDD.GQST.regular_copy_graph_fin S.gq_W (S.q + 3)
    (by omega) (by omega) hw hm
  obtain ⟨h1, h2, h3⟩ := BipartiteDD.GQST.regular_comap (finCongr hn) H (S.q + 3) hc hd he
  exact ⟨H.comap (finCongr hn).symm, h1, h2, h3⟩

end Setting

/-! The field `GF(13^4)`, the Singer setting for `q = 13`, and the 5440-vertex instance. -/

instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- `GF(13⁴)`, the field of the Singer setting for `q = 13`. -/
abbrev F13 := GaloisField 13 4

noncomputable instance : Fintype F13 := Fintype.ofFinite F13

/-- The Singer setting for `q = 13`: `F13` has `13⁴` elements and its unit group is cyclic. -/
noncomputable def setting13 : Setting F13 13 where
  e := 1
  odd_p := by decide
  card_eq := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 13 4 (by norm_num)]
    norm_num
  g := ((IsCyclic.exists_generator (α := F13ˣ)).choose : F13ˣ)
  orderOf_g := by
    have hg := (IsCyclic.exists_generator (α := F13ˣ)).choose_spec
    rw [orderOf_units, orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units,
      Nat.card_eq_fintype_card]

/-- Step 3 of the brief: a 16-regular bipartite graph of diameter at most 4 on 5440 vertices. -/
theorem regular5440 :
    ∃ H : SimpleGraph (Fin 5440), H.Colorable 2 ∧ (∀ v, (H.neighborSet v).ncard = 16) ∧
      H.ediam ≤ 4 := by
  obtain ⟨H, hc, hd, he⟩ := Setting.regular_W3 setting13
  have hq : setting13.q = 13 := rfl
  have h5 : 2 * (setting13.q ^ 2 + 1) * (setting13.q + 3) = 5440 := by
    rw [hq]
    norm_num
  have hd' : ∀ v, (H.neighborSet v).ncard = 16 := fun v => (hd v).trans (by rw [hq])
  obtain ⟨h1, h2, h3⟩ := BipartiteDD.GQST.regular_comap (finCongr h5) H 16 hc hd' he
  exact ⟨H.comap (finCongr h5).symm, h1, h2, h3⟩

end BipartiteDD.SingerC
