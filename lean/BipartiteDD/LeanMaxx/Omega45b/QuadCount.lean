import BipartiteDD.LeanMaxx.Omega45b.Zcount

/-!
# Omega45b.QuadCount: zeros of `Qf` on `⟨y, y'⟩^⊥` and `⟨y, y', y''⟩^⊥` over `F7`

For independent singular vectors `s₁, …, s_k` of `F7^7` (`k = 2, 3`), let `U = ⟨s⟩^⊥` for the polar
form `Bf`, a subspace of dimension `7 - k`. We count the zeros of `Qf` on `U`:
* `card_perpZeros_two`: for `k = 2` there are exactly `7^4 = 2401`;
* `card_perpZeros_three_le`: for `k = 3` there are at most `385`.

Method. `Qf` restricted to `U` is a quadratic form, isometric to a diagonal form `Σ wᵢ xᵢ²`
(`QuadraticForm.equivalent_weightedSumSquares`), so the zero count is `wzeros w` (`Zcount`). The
radical of `Bf` on `U` is `U ∩ U^⊥ = U ∩ ⟨s⟩` (`orthogonal_orthogonal`). On the diagonal side it
has `7 ^ nzero w` elements; on the other side it is the kernel of the Gram matrix `(Bf sᵢ sⱼ)`,
which is symmetric with zero diagonal (`exists_weights`). For `k = 2` that kernel has `1` or `49`
elements, so `nzero w ∈ {0, 2}`; for `k = 3` it has at most `7` elements unless the Gram matrix is
zero (`card_gram3_le`), so `nzero w ∈ {0, 1, 3}`.
-/

namespace BipartiteDD.LeanMaxx.Omega45b

open BipartiteDD.Hexagon Module

local instance : NeZero (2 : F7) := ⟨by decide⟩

local instance : Invertible (2 : F7) := ⟨4, by decide, by decide⟩

/-- `Qf` as a quadratic form, the diagonal of `x₀y₄ + x₁y₅ + x₂y₆ - x₃y₃`. -/
def QfQ : QuadraticForm F7 (V7 F7) :=
  LinearMap.BilinMap.toQuadraticMap <| LinearMap.mk₂ F7
    (fun x y : V7 F7 => x 0 * y 4 + x 1 * y 5 + x 2 * y 6 - x 3 * y 3)
    (fun x y z => by simp only [Pi.add_apply]; ring)
    (fun c x y => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun x y z => by simp only [Pi.add_apply]; ring)
    (fun c x y => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

theorem QfQ_apply (x : V7 F7) : QfQ x = Qf x := by
  simp only [QfQ, LinearMap.BilinMap.toQuadraticMap_apply, LinearMap.mk₂_apply, Qf]; ring

theorem Bf_self (x : V7 F7) : Bf x x = 2 * Qf x := by
  simp only [Bf, Qf]; ring

theorem BfForm_isRefl : (BfForm F7).IsRefl := fun x y h => by
  rw [BfForm_apply, Bf_comm]; exact h

/-- The radical of the polar form of a diagonal form `Σ wᵢ xᵢ²`. -/
theorem diag_rad {n : ℕ} (w v : Fin n → F7) :
    (∀ v' : Fin n → F7, ∑ i, 2 * w i * v i * v' i = 0) ↔ ∀ i, w i = 0 ∨ v i = 0 := by
  constructor
  · intro h i
    have := h (Pi.single i 1)
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true] at this
    rcases mul_eq_zero.1 this with h1 | h1
    · exact (mul_eq_zero.1 h1).resolve_left two_ne_zero |> Or.inl
    · exact Or.inr h1
  · intro h v'
    exact Finset.sum_eq_zero fun i _ => by rcases h i with h | h <;> simp [h]

theorem card_diag_rad {n : ℕ} (w : Fin n → F7) :
    Fintype.card {v : Fin n → F7 // ∀ i, w i = 0 ∨ v i = 0} = 7 ^ nzero w := by
  have e : {v : Fin n → F7 // ∀ i, w i = 0 ∨ v i = 0} ≃ ({i // w i = 0} → F7) :=
    { toFun := fun v i => v.1 i
      invFun := fun g => ⟨fun i => if h : w i = 0 then g ⟨i, h⟩ else 0, fun i => by
        by_cases h : w i = 0 <;> simp [h]⟩
      left_inv := fun v => by
        ext i
        by_cases h : w i = 0
        · simp [h]
        · simp [h, (v.2 i).resolve_left h]
      right_inv := fun g => by ext i; simp [i.2] }
  rw [Fintype.card_congr e, Fintype.card_fun, ZMod.card, nzero, Fintype.card_subtype]

section general

variable {k : ℕ} (s : Fin k → V7 F7)

/-- The orthogonal complement (for `Bf`) of the span of the vectors `s i`. -/
def perpSp : Submodule F7 (V7 F7) := (BfForm F7).orthogonal (Submodule.span F7 (Set.range s))

variable {s}

theorem mem_perpSp {x : V7 F7} : x ∈ perpSp s ↔ ∀ i, Bf (s i) x = 0 := by
  rw [perpSp, LinearMap.BilinForm.mem_orthogonal_iff]
  refine ⟨fun h i => h _ (Submodule.subset_span ⟨i, rfl⟩), fun h n hn => ?_⟩
  have : Submodule.span F7 (Set.range s) ≤ LinearMap.ker ((BfForm F7).flip x) :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; simpa using h i)
  simpa using this hn

theorem finrank_perpSp (hs : LinearIndependent F7 s) : finrank F7 (perpSp s) + k = 7 := by
  have h1 := LinearMap.BilinForm.finrank_orthogonal BfForm_nondegenerate
    (Submodule.span F7 (Set.range s))
  have h2 := finrank_span_eq_card hs
  have h3 := Submodule.finrank_le (Submodule.span F7 (Set.range s))
  rw [finrank_V7] at h1 h3
  rw [Fintype.card_fin] at h2
  rw [perpSp, h1]
  omega

/-- The radical of `Bf` on `perpSp s` is `span s ∩ perpSp s`. -/
theorem mem_span_iff_perp {x : V7 F7} :
    x ∈ Submodule.span F7 (Set.range s) ↔ ∀ z ∈ perpSp s, Bf x z = 0 := by
  conv_lhs => rw [← LinearMap.BilinForm.orthogonal_orthogonal BfForm_nondegenerate BfForm_isRefl
    (Submodule.span F7 (Set.range s))]
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  refine forall₂_congr fun z _ => ?_
  rw [BfForm_apply, Bf_comm]

theorem Bf_sum (x : V7 F7) (c : Fin k → F7) : Bf x (∑ j, c j • s j) = ∑ j, c j * Bf x (s j) := by
  rw [← BfForm_apply, map_sum]
  simp

/-- Diagonalisation of `Qf` on `⟨s⟩^⊥`: the zero count is `wzeros w`, and `7 ^ nzero w` is the size
of the kernel of the Gram matrix `(Bf sᵢ sⱼ)`. -/
theorem exists_weights (hs : LinearIndependent F7 s) {n : ℕ} (hn : n + k = 7) :
    ∃ w : Fin n → F7,
      wzeros w = (Finset.univ.filter fun x : V7 F7 => Qf x = 0 ∧ ∀ i, Bf x (s i) = 0).card ∧
      7 ^ nzero w = (Finset.univ.filter fun c : Fin k → F7 =>
        ∀ i, ∑ j, c j * Bf (s i) (s j) = 0).card := by
  have hU : finrank F7 (perpSp s) = n := by have := finrank_perpSp hs; omega
  subst hU
  obtain ⟨w, ⟨e⟩⟩ := QuadraticForm.equivalent_weightedSumSquares (QfQ.comp (perpSp s).subtype)
  have he : ∀ u, ∑ i, w i * e u i ^ 2 = Qf u := by
    intro u
    have := e.map_app u
    simp only [QuadraticMap.weightedSumSquares_apply, QuadraticMap.comp_apply,
      Submodule.subtype_apply, QfQ_apply, smul_eq_mul] at this
    rw [← this]
    simp [sq]
  have hB : ∀ u z : perpSp s, Bf u z = ∑ i, 2 * w i * e u i * e z i := by
    intro u z
    rw [show Bf (u : V7 F7) z = Qf ((u : V7 F7) + (z : V7 F7)) - Qf (u : V7 F7) - Qf (z : V7 F7) 
        by rw [Qf_add]; ring,
      ← Submodule.coe_add, ← he, ← he, ← he, map_add, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply]
    ring
  refine ⟨w, ?_, ?_⟩
  · rw [wzeros, ← Fintype.card_subtype, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
      ← Nat.card_eq_fintype_card]
    symm
    calc Nat.card {x : V7 F7 // Qf x = 0 ∧ ∀ i, Bf x (s i) = 0}
        = Nat.card {u : ↥(perpSp s) // Qf (u : V7 F7) = 0} := Nat.card_congr <|
          (Equiv.subtypeEquivRight (q := fun x => x ∈ perpSp s ∧ Qf x = 0) fun x =>
            ⟨fun ⟨h1, h2⟩ => ⟨mem_perpSp.2 fun i => by rw [Bf_comm]; exact h2 i, h1⟩,
              fun ⟨h1, h2⟩ => ⟨h2, fun i => by rw [Bf_comm]; exact mem_perpSp.1 h1 i⟩⟩).trans
          (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ perpSp s) (fun x => Qf x = 0)).symm
      _ = _ := Nat.card_congr <| e.toLinearEquiv.toEquiv.subtypeEquiv fun u => by
          rw [← he u]
          rfl
  · rw [← card_diag_rad, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
      ← Nat.card_eq_fintype_card]
    calc Nat.card {v : Fin (finrank F7 (perpSp s)) → F7 // ∀ i, w i = 0 ∨ v i = 0}
        = Nat.card {u : ↥(perpSp s) // ∀ z ∈ perpSp s, Bf (u : V7 F7) z = 0} := by
          refine (Nat.card_congr <| e.toLinearEquiv.toEquiv.subtypeEquiv fun u => ?_).symm
          rw [← diag_rad]
          refine ⟨fun h v' => ?_, fun h z hz => ?_⟩
          · obtain ⟨z, rfl⟩ := e.surjective v'
            exact (hB u z).symm.trans (h z z.2)
          · exact (hB u ⟨z, hz⟩).trans (h _)
      _ = Nat.card {x : V7 F7 // x ∈ perpSp s ∧ x ∈ Submodule.span F7 (Set.range s)} :=
          Nat.card_congr <|
          (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ perpSp s)
            (fun x => ∀ z ∈ perpSp s, Bf x z = 0)).trans
          (Equiv.subtypeEquivRight
            (q := fun x => x ∈ perpSp s ∧ x ∈ Submodule.span F7 (Set.range s))
            fun x => and_congr_right fun _ => mem_span_iff_perp.symm)
      _ = _ := by
          refine (Nat.card_congr (Equiv.ofBijective (fun c => ⟨∑ j, c.1 j • s j,
            mem_perpSp.2 fun i => by rw [Bf_sum]; exact c.2 i,
            Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
              (Submodule.subset_span ⟨j, rfl⟩)⟩) ⟨?_, ?_⟩)).symm
          · rintro ⟨c, hc⟩ ⟨c', hc'⟩ h
            exact Subtype.ext (funext (Fintype.linearIndependent_iffₛ.1 hs c c'
              (congrArg Subtype.val h)))
          · rintro ⟨x, hx1, hx2⟩
            obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun F7).1 hx2
            refine ⟨⟨c, fun i => ?_⟩, rfl⟩
            rw [← Bf_sum]
            exact mem_perpSp.1 hx1 i

end general

theorem card_perpZeros_two {y y' : V7 F7} (hy : Qf y = 0) (hy' : Qf y' = 0)
    (hli : LinearIndependent F7 ![y, y']) : (perpZeros [y, y']).card = 2401 := by
  obtain ⟨w, h1, h2⟩ := exists_weights hli (n := 5) rfl
  simp [Fin.forall_fin_succ, Fin.sum_univ_succ, Bf_self, hy, hy'] at h2
  rw [Bf_comm y' y] at h2
  have hP : perpZeros [y, y'] =
      Finset.univ.filter fun x : V7 F7 => Qf x = 0 ∧ ∀ i, Bf x (![y, y'] i) = 0 := by
    ext x
    simp [perpZeros, Fin.forall_fin_succ]
  rw [hP, ← h1]
  apply wzeros5
  by_cases ha : Bf y y' = 0
  · simp only [ha, or_true, and_self] at h2
    rw [Finset.filter_true_of_mem (fun _ _ => trivial), Finset.card_univ, Fintype.card_fun,
      ZMod.card, Fintype.card_fin] at h2
    exact Or.inr (Nat.pow_right_injective (by norm_num) h2)
  · simp only [ha, or_false] at h2
    have h3 : (Finset.univ.filter fun x : Fin 2 → F7 => x 1 = 0 ∧ x 0 = 0).card ≤ 1 :=
      Finset.card_le_one.2 fun x hx x' hx' => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
        ext i; fin_cases i
        · exact hx.2.trans hx'.2.symm
        · exact hx.1.trans hx'.1.symm
    have h4 : nzero w ≤ 0 :=
      (Nat.pow_le_pow_iff_right (by norm_num)).1 ((h2.trans_le h3).trans (pow_zero 7).ge)
    omega

/-- A nonzero `3 × 3` symmetric matrix with zero diagonal has rank `≥ 2`: its kernel has `≤ 7`
elements (a kernel vector is determined by one coordinate). -/
theorem card_gram3_le {a b c : F7} (h : ¬(a = 0 ∧ b = 0 ∧ c = 0)) :
    (Finset.univ.filter fun x : Fin 3 → F7 =>
      x 1 * a + x 2 * b = 0 ∧ x 0 * a + x 2 * c = 0 ∧ x 0 * b + x 1 * c = 0).card ≤ 7 := by
  have key : ∃ j : Fin 3, Set.InjOn (fun x : Fin 3 → F7 => x j) ↑(Finset.univ.filter
      fun x : Fin 3 → F7 =>
        x 1 * a + x 2 * b = 0 ∧ x 0 * a + x 2 * c = 0 ∧ x 0 * b + x 1 * c = 0) := by
    by_cases ha : a = 0
    · by_cases hb : b = 0
      · have hc : c ≠ 0 := fun hc => h ⟨ha, hb, hc⟩
        refine ⟨0, fun x hx x' hx' (he : x 0 = x' 0) => ?_⟩
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx hx'
        have h1 : x 1 = x' 1 := mul_right_cancel₀ hc
          (by linear_combination hx.2.2 - hx'.2.2 - b * he)
        have h2 : x 2 = x' 2 := mul_right_cancel₀ hc
          (by linear_combination hx.2.1 - hx'.2.1 - a * he)
        ext i; fin_cases i; exacts [he, h1, h2]
      · refine ⟨1, fun x hx x' hx' (he : x 1 = x' 1) => ?_⟩
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx hx'
        have h0 : x 0 = x' 0 := mul_right_cancel₀ hb
          (by linear_combination hx.2.2 - hx'.2.2 - c * he)
        have h2 : x 2 = x' 2 := mul_right_cancel₀ hb
          (by linear_combination hx.1 - hx'.1 - a * he)
        ext i; fin_cases i; exacts [h0, he, h2]
    · refine ⟨2, fun x hx x' hx' (he : x 2 = x' 2) => ?_⟩
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx hx'
      have h0 : x 0 = x' 0 := mul_right_cancel₀ ha
        (by linear_combination hx.2.1 - hx'.2.1 - c * he)
      have h1 : x 1 = x' 1 := mul_right_cancel₀ ha
        (by linear_combination hx.1 - hx'.1 - b * he)
      ext i; fin_cases i; exacts [h0, h1, he]
  obtain ⟨j, hj⟩ := key
  calc _ ≤ (Finset.univ : Finset F7).card :=
        Finset.card_le_card_of_injOn _ (fun _ _ => by simp) hj
    _ = 7 := by simp

theorem card_perpZeros_three_le {y y' y'' : V7 F7} (hy : Qf y = 0) (hy' : Qf y' = 0)
    (hy'' : Qf y'' = 0) (hli : LinearIndependent F7 ![y, y', y'']) :
    (perpZeros [y, y', y'']).card ≤ 385 := by
  obtain ⟨w, h1, h2⟩ := exists_weights hli (n := 4) rfl
  simp [Fin.forall_fin_succ, Fin.sum_univ_succ, Bf_self, hy, hy', hy''] at h2
  rw [Bf_comm y' y, Bf_comm y'' y, Bf_comm y'' y'] at h2
  have hP : perpZeros [y, y', y''] =
      Finset.univ.filter fun x : V7 F7 => Qf x = 0 ∧ ∀ i, Bf x (![y, y', y''] i) = 0 := by
    ext x
    simp [perpZeros, Fin.forall_fin_succ]
  rw [hP, ← h1]
  apply wzeros4
  by_cases h0 : Bf y y' = 0 ∧ Bf y y'' = 0 ∧ Bf y' y'' = 0
  · rw [h0.1, h0.2.1, h0.2.2] at h2
    simp only [mul_zero, add_zero, and_self] at h2
    rw [Finset.filter_true_of_mem (fun _ _ => trivial), Finset.card_univ, Fintype.card_fun,
      ZMod.card, Fintype.card_fin] at h2
    exact Or.inr (Or.inr (Nat.pow_right_injective (by norm_num) h2))
  · have h3 := h2.trans_le (card_gram3_le h0)
    have h4 : nzero w ≤ 1 := (Nat.pow_le_pow_iff_right (by norm_num)).1 (h3.trans (pow_one 7).ge)
    omega

end BipartiteDD.LeanMaxx.Omega45b
