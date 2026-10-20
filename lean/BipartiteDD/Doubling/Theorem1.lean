import BipartiteDD.Doubling.LevelsDegree

/-! Group Doubling, part 5: Theorem 1 of `research/p4/hats/REPORT.md` (Delorme 1985, Sec. 7), in the
form with levels `A₀ ⊇ A₁ ⊇ …`.

`height A hfin v` is the number of levels containing `v` (the least `i` with `v ∉ A i`), so
`A i = {v | i < height v}` (`lt_height_iff`); a vertex of level `k` has height `k + 1`. The theorem is
`levelled_levels`: with hypotheses (a), (b), (c) of the report,
* `levelled G m (height A hfin)` is bipartite, of maximum degree at most `Δ + (m - 1)` and diameter at most
  `D` (`isBipartiteDegDiam_levelled`);
* its number of vertices is `|V| + (m - 1) (|A₀| + m |A₁| + m² |A₂| + …)` (`card_levelled_levels`).

`D ≥ 2` is not used. -/

namespace BipartiteDD.Doubling

open SimpleGraph
open scoped Classical

variable {V : Type*}

/-- The height of a vertex: the number of levels `A i` containing it. -/
noncomputable def height (A : ℕ → Set V) (hfin : ∀ v, ∃ i, v ∉ A i) (v : V) : ℕ :=
  Nat.find (hfin v)

section Height

variable {A : ℕ → Set V} {hfin : ∀ v, ∃ i, v ∉ A i}

/-- `A i = {v | i < height v}`. -/
theorem lt_height_iff (hA : Antitone A) {i : ℕ} {v : V} : i < height A hfin v ↔ v ∈ A i := by
  constructor
  · intro hi
    by_contra hv
    exact Nat.find_min (hfin v) hi hv
  · intro hv
    by_contra hle
    have hle' : height A hfin v ≤ i := not_lt.1 hle
    exact Nat.find_spec (hfin v) (hA hle' hv)

theorem height_le {K : ℕ} {v : V} (hv : v ∉ A K) : height A hfin v ≤ K :=
  Nat.find_min' (hfin v) hv

end Height

/-! ### Order -/

/-- Geometric sum: `m ^ n = 1 + (m - 1) (1 + m + … + m ^ (n - 1))`. -/
theorem pow_eq_one_add_mul_geom (m n : ℕ) (hm : 0 < m) :
    m ^ n = 1 + (m - 1) * ∑ i ∈ Finset.range n, m ^ i := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.add_sub_cancel]
    simp only [Nat.add_sub_cancel] at ih
    calc (k + 1) ^ (n + 1) = (k + 1) ^ n + k * (k + 1) ^ n := by ring
      _ = (1 + k * ∑ i ∈ Finset.range n, (k + 1) ^ i) + k * (k + 1) ^ n := by rw [← ih]
      _ = 1 + k * (∑ i ∈ Finset.range n, (k + 1) ^ i + (k + 1) ^ n) := by ring

/-- The number of versions, in terms of heights: `∑ m ^ h v = |V| + (m - 1) ∑_i m ^ i #{v | i < h v}`,
for `h v ≤ K`. -/
theorem sum_pow_height [Fintype V] {m K : ℕ} (hm : 0 < m) {h : V → ℕ} (hK : ∀ v, h v ≤ K) :
    ∑ v, m ^ h v = Fintype.card V +
      (m - 1) * ∑ i ∈ Finset.range K, m ^ i * (Finset.univ.filter (fun v => i < h v)).card := by
  have h1 : ∀ v, m ^ h v = 1 + (m - 1) * ∑ i ∈ Finset.range K, if i < h v then m ^ i else 0 := by
    intro v
    rw [pow_eq_one_add_mul_geom m (h v) hm]
    congr 2
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    have := hK v
    omega
  simp_rw [h1]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
    ← Finset.mul_sum, Finset.sum_comm]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_comm]

/-! ### Theorem 1 -/

section Theorem1

variable {G : SimpleGraph V} {A : ℕ → Set V}

/-- Group Doubling, Theorem 1 (bipartite, degree, diameter). Levels `A 0 ⊇ A 1 ⊇ …` with `A K = ∅`;
(a): `N(A_{i+1}) ⊆ A_i` and each vertex of `A_i ∖ A_{i+1}` has at most one neighbour in `A_{i+1}`;
(b): each vertex outside `A₀` has at most one neighbour in `A₀`; (c): `CondC G A₀ D`. -/
theorem isBipartiteDegDiam_levelled [Finite V] {Δ D m : ℕ} (hm : 0 < m)
    (hG : IsBipartiteDegDiam G Δ D) (hA : Antitone A) {K : ℕ} (hK : A K = ∅)
    (ha1 : ∀ i, ∀ v ∈ A (i + 1), ∀ u, G.Adj u v → u ∈ A i)
    (ha2 : ∀ i, ∀ u ∈ A i, u ∉ A (i + 1) → (G.neighborSet u ∩ A (i + 1)).ncard ≤ 1)
    (hb : ∀ u, u ∉ A 0 → (G.neighborSet u ∩ A 0).ncard ≤ 1)
    (hc : CondC G (A 0) D) :
    IsBipartiteDegDiam
      (levelled G m (height A (fun v => ⟨K, by simp [hK]⟩))) (Δ + (m - 1)) D := by
  set hfin : ∀ v, ∃ i, v ∉ A i := fun v => ⟨K, by simp [hK]⟩ with hfin_def
  have hmem : ∀ i v, i < height A hfin v ↔ v ∈ A i := fun i v => lt_height_iff hA
  refine ⟨levelled_colorable hG.1, ?_, ?_⟩
  · refine fun x => levelled_degree hm hG.2.1 ?_ ?_ x
    · -- a neighbour has height at most one more
      intro u v huv
      by_contra hlt
      have hv : v ∈ A (height A hfin u + 1) := (hmem _ _).1 (by omega)
      have := (hmem _ _).2 (ha1 _ v hv u huv)
      omega
    · -- at most one neighbour is higher
      intro u
      have hset : {v | G.Adj u v ∧ height A hfin u < height A hfin v} =
          G.neighborSet u ∩ A (height A hfin u) := by
        ext v
        simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, mem_neighborSet, hmem]
      rw [hset]
      rcases Nat.eq_zero_or_pos (height A hfin u) with h0 | hpos
      · rw [h0]
        exact hb u (fun hu => by have := (hmem 0 u).2 hu; omega)
      · obtain ⟨i, hi⟩ : ∃ i, height A hfin u = i + 1 := ⟨height A hfin u - 1, by omega⟩
        rw [hi]
        refine ha2 i u ((hmem i u).1 (by omega)) (fun hu => ?_)
        have := (hmem (i + 1) u).2 hu
        omega
  · refine levelled_ediam hm hG.2.2 ?_
    have : {v | 0 < height A hfin v} = A 0 := Set.ext fun v => hmem 0 v
    rw [this]
    exact hc

/-- Group Doubling, Theorem 1 (order). The number of vertices of the levelled doubling is
`|V| + (m - 1) (|A₀| + m |A₁| + m² |A₂| + …)`. -/
theorem card_levelled_levels [Fintype V] {m : ℕ} (hm : 0 < m) (hA : Antitone A) {K : ℕ}
    (hK : A K = ∅) :
    Nat.card (Ver V m (height A (fun v => ⟨K, by simp [hK]⟩))) =
      Nat.card V + (m - 1) * ∑ i ∈ Finset.range K, m ^ i * (A i).ncard := by
  set hfin : ∀ v, ∃ i, v ∉ A i := fun v => ⟨K, by simp [hK]⟩ with hfin_def
  have hmem : ∀ i v, i < height A hfin v ↔ v ∈ A i := fun i v => lt_height_iff hA
  have hcard : ∀ i, (Finset.univ.filter (fun v => i < height A hfin v)).card = (A i).ncard := by
    intro i
    rw [← Set.ncard_coe_finset]
    congr 1
    ext v
    simp [hmem]
  rw [card_levelled, Nat.card_eq_fintype_card (α := V),
    sum_pow_height hm (h := height A hfin) (K := K) (fun v => height_le (by simp [hK]))]
  simp only [hcard]

/-- Group Doubling, Theorem 1, transported to `Fin n` with `n = |V| + (m - 1) (|A₀| + m |A₁| + …)`. -/
theorem delorme_levelled [Fintype V] {Δ D m : ℕ} (hm : 0 < m) (hG : IsBipartiteDegDiam G Δ D)
    (hA : Antitone A) {K : ℕ} (hK : A K = ∅)
    (ha1 : ∀ i, ∀ v ∈ A (i + 1), ∀ u, G.Adj u v → u ∈ A i)
    (ha2 : ∀ i, ∀ u ∈ A i, u ∉ A (i + 1) → (G.neighborSet u ∩ A (i + 1)).ncard ≤ 1)
    (hb : ∀ u, u ∉ A 0 → (G.neighborSet u ∩ A 0).ncard ≤ 1)
    (hc : CondC G (A 0) D) :
    ∃ H : SimpleGraph (Fin (Nat.card V + (m - 1) * ∑ i ∈ Finset.range K, m ^ i * (A i).ncard)),
      IsBipartiteDegDiam H (Δ + (m - 1)) D := by
  have hcard := card_levelled_levels hm hA hK
  have hfinite : Finite (Ver V m (height A (fun v => ⟨K, by simp [hK]⟩))) := inferInstance
  let e := (Finite.equivFin (Ver V m (height A (fun v => ⟨K, by simp [hK]⟩)))).trans
    (finCongr hcard)
  exact ⟨_, isBipartiteDegDiam_comap e
    (isBipartiteDegDiam_levelled hm hG hA hK ha1 ha2 hb hc)⟩

end Theorem1

end BipartiteDD.Doubling
