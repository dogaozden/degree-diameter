import BipartiteDD.LeanMaxx.Singer.Setting
import BipartiteDD.SingerC.Regular5440

/-! Corollary C1 and the regular copy graph of `W(3,q)`, for every odd prime power `q`.

These instantiate `SingerC.Setting.corC1` and `SingerC.Setting.regular_W3` at the Setting of
`Setting.lean`, so no field data is fixed in the statements: `q` ranges over odd prime powers. -/

namespace BipartiteDD.LeanMaxx.Singer

open BipartiteDD.SingerC

/-- Transport a graph witness along equal vertex counts and equal parameters. -/
theorem transport {n n' d d' D : ℕ} (hn : n = n') (hd : d = d') {H : SimpleGraph (Fin n)}
    (h : IsBipartiteDegDiam H d D) : ∃ H' : SimpleGraph (Fin n'), IsBipartiteDegDiam H' d' D := by
  subst hn
  subst hd
  exact ⟨H, h⟩

/-- Corollary C1 for every odd prime power `q`: for every even `j ≥ 2` there is a bipartite graph
on `2 (q ^ 2 + 1) (q + 1 + j)` vertices with maximum degree at most `q + 1 + j` and diameter at most
`4`. -/
theorem corC1_all {q : ℕ} (hq : IsPrimePow q) (hodd : Odd q) {j : ℕ} (hj : Even j) (hj2 : 2 ≤ j) :
    ∃ H : SimpleGraph (Fin (2 * (q ^ 2 + 1) * (q + 1 + j))),
      IsBipartiteDegDiam H (q + 1 + j) 4 := by
  obtain ⟨p, e, hp, he, rfl⟩ := (isPrimePow_nat_iff q).mp hq
  have : Fact p.Prime := ⟨hp⟩
  have hodd' : Odd p := (Nat.odd_pow_iff (by omega)).mp hodd
  obtain ⟨S, hS⟩ := setting_exists p hodd' e he
  obtain ⟨H, hH⟩ := S.corC1 hj hj2
  exact transport (by rw [hS]) (by rw [hS]) hH

/-- The regular copy graph of `W(3,q)` for every odd prime power `q`: a `(q + 3)`-regular bipartite
graph on `2 (q ^ 2 + 1) (q + 3)` vertices of diameter at most `4`. -/
theorem regular_W3_all {q : ℕ} (hq : IsPrimePow q) (hodd : Odd q) :
    ∃ H : SimpleGraph (Fin (2 * (q ^ 2 + 1) * (q + 3))),
      H.Colorable 2 ∧ (∀ v, (H.neighborSet v).ncard = q + 3) ∧ H.ediam ≤ 4 := by
  obtain ⟨p, e, hp, he, rfl⟩ := (isPrimePow_nat_iff q).mp hq
  have : Fact p.Prime := ⟨hp⟩
  have hodd' : Odd p := (Nat.odd_pow_iff (by omega)).mp hodd
  obtain ⟨S, hS⟩ := setting_exists p hodd' e he
  obtain ⟨H, hc, hd, h4⟩ := S.regular_W3
  have hn : 2 * (S.q ^ 2 + 1) * (S.q + 3) = 2 * ((p ^ e) ^ 2 + 1) * (p ^ e + 3) := by rw [hS]
  have hd' : ∀ v, (H.neighborSet v).ncard = p ^ e + 3 := fun v => (hd v).trans (by rw [hS])
  obtain ⟨h1, h2, h3⟩ := BipartiteDD.GQST.regular_comap (finCongr hn) H (p ^ e + 3) hc hd' h4
  exact ⟨H.comap (finCongr hn).symm, h1, h2, h3⟩

end BipartiteDD.LeanMaxx.Singer
