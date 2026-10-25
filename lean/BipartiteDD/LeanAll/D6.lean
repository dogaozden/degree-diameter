import BipartiteDD.HexagonD.TheoremD
import Mathlib.FieldTheory.Finite.GaloisField

/-! The diameter-6 records `(11,6)`, `(13,6)`, `(15,6)`, `(16,6)` as instances of Theorem D
(`HexagonD.theoremD`, `HexagonD.theoremD_two`: Delorme's doubling of the split Cayley hexagon `H(q)` with
exact whiskers, for every finite field of odd characteristic).

| cell | q | m | vertices |
|---|---|---|---|
| (11,6) | 9  | 2 | 148,944 |
| (13,6) | 11 | 2 | 388,972 |
| (15,6) | 13 | 2 | 870,440 |
| (16,6) | 13 | 3 | 940,846 |
-/

namespace BipartiteDD.LeanAll

open BipartiteDD.HexagonD

instance fact_prime_3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
instance fact_prime_11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩
instance fact_prime_13 : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- `GF(9)` with a `Fintype` structure. -/
noncomputable instance fintypeGF9 : Fintype (GaloisField 3 2) := Fintype.ofFinite _

theorem card_GF9 : Fintype.card (GaloisField 3 2) = 9 := by
  rw [Fintype.card_eq_nat_card, GaloisField.card 3 2 (by norm_num)]
  norm_num

instance neZero_two_GF9 : NeZero (2 : GaloisField 3 2) :=
  ⟨fun h => by
    have h' : ((2 : ℕ) : GaloisField 3 2) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (GaloisField 3 2) 3] at h'
    norm_num at h'⟩

instance neZero_two_Z11 : NeZero (2 : ZMod 11) := ⟨by decide⟩
instance neZero_two_Z13 : NeZero (2 : ZMod 13) := ⟨by decide⟩

end BipartiteDD.LeanAll

open BipartiteDD.LeanAll BipartiteDD.HexagonD in
/-- `(11,6)`: Theorem D over `GF(9)`, `Δ = q + 2`. -/
theorem nb_11_6 : ∃ G : SimpleGraph (Fin 148944), BipartiteDD.IsBipartiteDegDiam G 11 6 := by
  have h := theoremD_two (F := GaloisField 3 2)
  rw [card_GF9] at h
  exact h

open BipartiteDD.LeanAll BipartiteDD.HexagonD in
/-- `(13,6)`: Theorem D over `GF(11)`, `Δ = q + 2`. -/
theorem nb_13_6 : ∃ G : SimpleGraph (Fin 388972), BipartiteDD.IsBipartiteDegDiam G 13 6 := by
  have h := theoremD_two (F := ZMod 11)
  rw [ZMod.card] at h
  exact h

open BipartiteDD.LeanAll BipartiteDD.HexagonD in
/-- `(15,6)`: Theorem D over `GF(13)`, `Δ = q + 2`. -/
theorem nb_15_6 : ∃ G : SimpleGraph (Fin 870440), BipartiteDD.IsBipartiteDegDiam G 15 6 := by
  have h := theoremD_two (F := ZMod 13)
  rw [ZMod.card] at h
  exact h

open BipartiteDD.LeanAll BipartiteDD.HexagonD in
/-- `(16,6)`: Theorem D over `GF(13)` with `m = 3`, `Δ = q + 3`. -/
theorem nb_16_6 : ∃ G : SimpleGraph (Fin 940846), BipartiteDD.IsBipartiteDegDiam G 16 6 := by
  have h := theoremD (F := ZMod 13) (m := 3) (by norm_num)
  rw [ZMod.card] at h
  exact h

