import BipartiteDD.LeanMaxx.D5.Axioms
open BipartiteDD BipartiteDD.LeanMaxx.D5 BipartiteDD.SingerC

theorem setting_exists (p : ℕ) [hp : Fact p.Prime] (hodd : Odd p) (e : ℕ)
    (K : Type) [Field K] [Fintype K] [CharP K p] (hK : Fintype.card K = (p ^ e) ^ 4) :
    ∃ S : Setting K p, S.q = p ^ e := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  refine ⟨{ e := e, odd_p := hodd, card_eq := hK, g := (g : K), orderOf_g := ?_ }, rfl⟩
  rw [orderOf_units, orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units,
      Nat.card_eq_fintype_card]

theorem field_exists (p : ℕ) [hp : Fact p.Prime] (e : ℕ) (he : 0 < e) :
    ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K p), Fintype.card K = (p ^ e) ^ 4 := by
  haveI : NeZero (4 * e) := ⟨by omega⟩
  haveI : Fintype (GaloisField p (4 * e)) := Fintype.ofFinite _
  refine ⟨GaloisField p (4 * e), inferInstance, inferInstance, inferInstance, ?_⟩
  rw [← Nat.card_eq_fintype_card, GaloisField.card p (4 * e) (by omega)]
  rw [← pow_mul]; ring_nf

/-- For every odd prime `p`, every `e ≥ 1`, and `1 ≤ k ≤ p^e - 3`: a bipartite graph with max degree `p^e + 4`,
diameter ≤ 5, on `14 (q+1)(q²+1) + 2k` vertices, `q = p^e`. -/
theorem family_all_odd (p : ℕ) [hp : Fact p.Prime] (hodd : Odd p) (e : ℕ) (he : 0 < e) (k : ℕ)
    (hk1 : 1 ≤ k) (hkq : k + 3 ≤ p ^ e) :
    ∃ Y : SimpleGraph (Fin (14 * (((p ^ e) + 1) * ((p ^ e) ^ 2 + 1)) + k + k)),
      IsBipartiteDegDiam Y ((p ^ e) + 1 + 3) 5 := by
  obtain ⟨K, _, _, _, hK⟩ := field_exists p e he
  obtain ⟨S, hS⟩ := setting_exists p hodd e K hK
  have := S.family_odd hk1 (by rw [hS]; exact hkq)
  rw [hS] at this
  exact this

#print axioms setting_exists
#print axioms field_exists
#print axioms family_all_odd
-- smallest nontrivial case: q = 5, k = 2 (Delta = 9, 14*6*26 + 4 = 2188 vertices)
example : ∃ Y : SimpleGraph (Fin (14 * ((5 + 1) * (5 ^ 2 + 1)) + 2 + 2)), IsBipartiteDegDiam Y (5 + 1 + 3) 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  simpa using family_all_odd 5 (by decide) 1 (by omega) 2 (by omega) (by norm_num)
