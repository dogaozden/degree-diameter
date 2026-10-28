import BipartiteDD.LeanMaxx.D7Family.Even

/-! The infinite family of the diameter-7 note, stated for prime powers (research/theorems/D7_HEXAGON.md, Cor. 9.1).

`d7_family`: for every prime power `q ≥ 5` (`d7_family_odd`, `d7_family_even` are the two cases),
`n_b(q + 2, 7) ≥ 6 N(q) + 2 (q² + 1)`, `N(q) = (q⁶ - 1)/(q - 1)`, i.e. there is a bipartite graph on
`6 * ((q⁶ - 1)/(q - 1)) + 2 * (q² + 1)` vertices with maximum degree `q + 2` and diameter at most `7`.
It is `d7_odd` / `d7_even` for the Galois field of order `q`. -/

namespace BipartiteDD.LeanMaxx.D7Family

open SimpleGraph

theorem Nq_eq {q : ℕ} (hq : 2 ≤ q) : (q ^ 6 - 1) / (q - 1) = (q + 1) * (1 + q ^ 2 + q ^ 4) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have hr : 0 < r + 1 - 1 := by omega
  refine Nat.div_eq_of_eq_mul_left hr ?_
  rw [Nat.add_sub_cancel]
  apply Nat.sub_eq_of_eq_add
  ring

theorem d7_family_odd (q : ℕ) (hq : IsPrimePow q) (hodd : Odd q) (h5 : 5 ≤ q) :
    ∃ G : SimpleGraph (Fin (6 * ((q ^ 6 - 1) / (q - 1)) + 2 * (q ^ 2 + 1))),
      IsBipartiteDegDiam G (q + 2) 7 := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff q).1 hq
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hodd) ((Nat.even_pow' hk.ne').2 even_two)
  let K := GaloisField p k
  letI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = p ^ k := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card p k hk.ne'
  haveI : NeZero (2 : K) := ⟨fun h => hp2 (by
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 ((CharP.cast_eq_zero_iff K p 2).1 h'))⟩
  have h := d7_odd (F := K) (by rw [hcard]; exact h5)
  rw [hcard] at h
  rw [Nq_eq (by omega)]
  exact h

theorem d7_family_even (q : ℕ) (hq : IsPrimePow q) (heven : Even q) (h5 : 5 ≤ q) :
    ∃ G : SimpleGraph (Fin (6 * ((q ^ 6 - 1) / (q - 1)) + 2 * (q ^ 2 + 1))),
      IsBipartiteDegDiam G (q + 2) 7 := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff q).1 hq
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p = 2 := by
    have : 2 ∣ p ^ k := even_iff_two_dvd.1 heven
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 (Nat.prime_two.dvd_of_dvd_pow this)).symm
  subst hp2
  let K := GaloisField 2 k
  letI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 ^ k := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card 2 k hk.ne'
  have hchar : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have h := d7_even (F := K) hchar (by rw [hcard]; exact h5)
  rw [hcard] at h
  rw [Nq_eq (by omega)]
  exact h

/-- **The infinite family** (D7_HEXAGON.md, Cor. 9.1): for every prime power `q ≥ 5`,
`n_b(q + 2, 7) ≥ 6 N(q) + 2 (q² + 1)`, `N(q) = (q⁶ - 1)/(q - 1)`. -/
theorem d7_family (q : ℕ) (hq : IsPrimePow q) (h5 : 5 ≤ q) :
    ∃ G : SimpleGraph (Fin (6 * ((q ^ 6 - 1) / (q - 1)) + 2 * (q ^ 2 + 1))),
      IsBipartiteDegDiam G (q + 2) 7 :=
  (Nat.even_or_odd q).elim (fun he => d7_family_even q hq he h5) (fun ho => d7_family_odd q hq ho h5)

end BipartiteDD.LeanMaxx.D7Family
