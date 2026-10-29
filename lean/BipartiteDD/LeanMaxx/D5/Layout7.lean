import BipartiteDD.LeanMaxx.D5.Assemble
import BipartiteDD.LeanMaxx.D5.ThmB

/-! # D = 5 formalisation, part 9: the seven-level layout `HHHDHHD` over a quadrangle of order `(q, q)`

`research/theorems/D5_QUADRANGLE.md` Proposition 8.1 and Corollary 10.3 (with the non-friendly arcs left whole,
`c = 0`, and the complete bipartite hub graph (Y0) of Lemma 9.1).

Everything is written in the incidence structure `(P, L)` itself. A level of type `H` (class `A` = points of the
quadrangle `Q`) is, in `(P, L)`, a level with `A = L`; so `τ = true` on the levels `0, 1, 2, 4, 5` and `false` on
the `D`-levels `3, 6`. Rotational tournament on `Fin 7`: `i → i + 1, i + 2, i + 3`.

* arcs `H → D` (`0→3, 1→3, 2→3, 4→6, 5→6`): `M = id`, freed set = a set `S` of lines no two of which meet
  (a spread of `(P, L)`, an ovoid of the dual `Q`);
* arcs `D → H` (`3→4, 3→5, 6→0, 6→1, 6→2`): `M = id`, freed set = a set `Z` of points no two collinear (a partial
  ovoid of `(P, L)`);
* the eleven other arcs: `M = Φ` (a bijection `P ≃ L` extended to `P ⊕ L`), nothing freed;
* `K` hubs of each kind; the `𝓑`-hub `v` takes the slot `(s_v, i → 3|6|4|0)` and the `𝓐`-hub `u` the freed `𝓑`-slot
  `s_u`, with `s : Fin K ↪ S` or `Fin K ↪ Z`; the hub graph is complete bipartite (degree `K ≤ q - 3`).

`layout7` : `n_b(q + 4, 5) ≥ 14 N + 2K` in the form of an explicit graph on `7 (|P| + |L|) + 2K` vertices. -/

namespace BipartiteDD.LeanMaxx.D5

open SimpleGraph BipartiteDD Finset
open scoped Classical

set_option linter.unusedSectionVars false

variable {P L : Type*} [Membership P L] {ι V U : Type*}

/-- A bijection `P ≃ L` as an involution of `P ⊕ L` exchanging the two sides. -/
def Phi (e : P ≃ L) : P ⊕ L ≃ P ⊕ L where
  toFun
    | .inl p => .inr (e p)
    | .inr l => .inl (e.symm l)
  invFun
    | .inl p => .inr (e p)
    | .inr l => .inl (e.symm l)
  left_inv := by rintro (p | l) <;> simp
  right_inv := by rintro (p | l) <;> simp

theorem col_Phi (e : P ≃ L) (x : P ⊕ L) : col (Phi e x) = !col x := by
  rcases x with p | l <;> simp [Phi, col]

theorem col_Phi_symm (e : P ≃ L) (x : P ⊕ L) : col ((Phi e).symm x) = !col x := by
  rcases x with p | l <;> simp [Phi, col]

/-- The rotational tournament on `Fin 7`: `i → i + 1, i + 2, i + 3`. -/
def T7 (i j : Fin 7) : Prop := 1 ≤ (j.val + 7 - i.val) % 7 ∧ (j.val + 7 - i.val) % 7 ≤ 3

instance : DecidableRel T7 := fun i j => by unfold T7; infer_instance

/-- Types: `true` (= `H`, `A` = lines) on the levels `0, 1, 2, 4, 5`. -/
def tau7 : Fin 7 → Bool
  | 0 => true | 1 => true | 2 => true | 3 => false | 4 => true | 5 => true | 6 => false

/-- Source of the `D → H` / target of `H → D` arc taken by a `𝓑`-hub at level `i`. -/
def arcV7 : Fin 7 → Fin 7
  | 0 => 3 | 1 => 3 | 2 => 3 | 3 => 4 | 4 => 6 | 5 => 6 | 6 => 0

/-- Source level of the arc whose freed `𝓑`-slot an `𝓐`-hub takes at level `i`. -/
def arcU7 : Fin 7 → Fin 7
  | 0 => 6 | 1 => 6 | 2 => 6 | 3 => 0 | 4 => 3 | 5 => 3 | 6 => 4

theorem T7_irrefl : ∀ i j, T7 i j → i ≠ j := by decide
theorem T7_total : ∀ i j, i ≠ j → T7 i j ∨ T7 j i := by decide
theorem T7_anti : ∀ i j, T7 i j → ¬ T7 j i := by decide
theorem T7_out : ∀ i, (univ.filter (T7 i)).card = 3 := by decide
theorem arcV7_T : ∀ i, T7 i (arcV7 i) := by decide
theorem arcU7_T : ∀ i, T7 (arcU7 i) i := by decide
theorem arcV7_tau : ∀ i, tau7 (arcV7 i) = !tau7 i := by decide
theorem arcU7_tau : ∀ i, tau7 (arcU7 i) = !tau7 i := by decide

section Main

variable (e : P ≃ L) (S : Finset L) (Z : Finset P) {K : ℕ} (sp : Fin K → L) (zz : Fin K → P)

/-- Freed sets: the lines of `S` on `H → D` arcs, the points of `Z` on `D → H` arcs, nothing elsewhere. -/
def R7 (i j : Fin 7) : Set (P ⊕ L) :=
  if T7 i j ∧ tau7 i ≠ tau7 j then
    (if tau7 i = true then {x | ∃ l ∈ S, x = .inr l} else {x | ∃ p ∈ Z, x = .inl p})
  else ∅

/-- The data of the seven-level layout. -/
def D7 : Data P L (Fin 7) (Fin K) (Fin K) where
  T := T7
  τ := tau7
  M i j := if tau7 i = tau7 j then Phi e else Equiv.refl _
  R := R7 S Z
  slotV v i := if tau7 i = true then .inr (sp v) else .inl (zz v)
  slotU u i := if tau7 i = true then .inl (zz u) else .inr (sp u)
  NS _ _ := True

theorem M7_apply (i j : Fin 7) (x : P ⊕ L) :
    (D7 e S Z sp zz).M i j x = if tau7 i = tau7 j then Phi e x else x := by
  show (if tau7 i = tau7 j then Phi e else Equiv.refl _) x = _
  split_ifs <;> rfl

theorem M7_symm_apply (i j : Fin 7) (y : P ⊕ L) :
    ((D7 e S Z sp zz).M i j).symm y = if tau7 i = tau7 j then (Phi e).symm y else y := by
  show (if tau7 i = tau7 j then Phi e else Equiv.refl _).symm y = _
  split_ifs <;> rfl

theorem D7_hyp (hB : Base P L) : Hyp (D7 e S Z sp zz) where
  base := hB
  irrefl := T7_irrefl
  total := T7_total
  maps := by
    intro i j _ x hx
    have hx' : col x = tau7 i := hx
    rw [M7_apply]
    show col (if tau7 i = tau7 j then Phi e x else x) = !tau7 j
    by_cases h : tau7 i = tau7 j
    · rw [if_pos h, col_Phi, hx', h]
    · rw [if_neg h]
      have : tau7 j = !tau7 i := by cases h1 : tau7 i <;> cases h2 : tau7 j <;> simp_all
      rw [hx', this]; simp
  onto := by
    intro i j _ y hy
    have hy' : col y = !tau7 j := hy
    rw [M7_symm_apply]
    show col (if tau7 i = tau7 j then (Phi e).symm y else y) = tau7 i
    by_cases h : tau7 i = tau7 j
    · rw [if_pos h, col_Phi_symm, hy', h]; simp
    · rw [if_neg h]
      have : tau7 j = !tau7 i := by cases h1 : tau7 i <;> cases h2 : tau7 j <;> simp_all
      rw [hy', this]; simp
  slotA := by
    intro v i
    show col (if tau7 i = true then (Sum.inr (sp v) : P ⊕ L) else Sum.inl (zz v)) = tau7 i
    cases h : tau7 i <;> simp [col]
  slotB := by
    intro u i
    show col (if tau7 i = true then (Sum.inl (zz u) : P ⊕ L) else Sum.inr (sp u)) = !tau7 i
    cases h : tau7 i <;> simp [col]

theorem mem_R7 (i j : Fin 7) (x : P ⊕ L) :
    x ∈ R7 S Z i j ↔ T7 i j ∧ tau7 i ≠ tau7 j ∧
      ((tau7 i = true ∧ ∃ l ∈ S, x = .inr l) ∨ (tau7 i = false ∧ ∃ p ∈ Z, x = .inl p)) := by
  unfold R7
  by_cases h : T7 i j ∧ tau7 i ≠ tau7 j
  · have hj : tau7 j = !tau7 i := by
      have := h.2; cases h1 : tau7 i <;> cases h2 : tau7 j <;> simp_all
    rw [if_pos h]
    by_cases ht : tau7 i = true
    · rw [if_pos ht]; simp [h, ht, hj]
    · have : tau7 i = false := by simpa using ht
      rw [if_neg ht]; simp [h, this, hj]
  · rw [if_neg h]
    simp only [Set.mem_empty_iff_false, false_iff]
    intro hh
    exact h ⟨hh.1, hh.2.1⟩

theorem R7_col (i j : Fin 7) {x : P ⊕ L} (hx : x ∈ R7 S Z i j) : col x = tau7 i := by
  obtain ⟨-, -, ⟨hi, l, -, rfl⟩ | ⟨hi, p, -, rfl⟩⟩ := (mem_R7 S Z i j x).1 hx
  · simp [col, hi]
  · simp [col, hi]

theorem R7_empty (i j : Fin 7) (h : ¬ (T7 i j ∧ tau7 i ≠ tau7 j)) : R7 S Z i j = ∅ := by
  ext x
  rw [mem_R7]
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hh
  exact h ⟨hh.1, hh.2.1⟩

theorem R7_partial (hS : ∀ l ∈ S, ∀ l' ∈ S, l ≠ l' → ¬ Co (.inr l : P ⊕ L) (.inr l'))
    (hZ : ∀ p ∈ Z, ∀ p' ∈ Z, p ≠ p' → ¬ Co (.inl p : P ⊕ L) (.inl p')) (i j : Fin 7) :
    ∀ x ∈ R7 S Z i j, ∀ y ∈ R7 S Z i j, x ≠ y → ¬ Co x y := by
  intro x hx y hy hxy
  obtain ⟨-, -, ⟨hi, l, hl, rfl⟩ | ⟨hi, p, hp, rfl⟩⟩ := (mem_R7 S Z i j x).1 hx
  · obtain ⟨-, -, ⟨-, l', hl', rfl⟩ | ⟨hi', -⟩⟩ := (mem_R7 S Z i j y).1 hy
    · exact hS l hl l' hl' (fun h => hxy (by rw [h]))
    · rw [hi] at hi'; exact absurd hi' (by simp)
  · obtain ⟨-, -, ⟨hi', -⟩ | ⟨-, p', hp', rfl⟩⟩ := (mem_R7 S Z i j y).1 hy
    · rw [hi] at hi'; exact absurd hi' (by simp)
    · exact hZ p hp p' hp' (fun h => hxy (by rw [h]))

/-- Every arc of the layout is repaired. -/
theorem D7_repaired (hB : Base P L)
    (hS : ∀ l ∈ S, ∀ l' ∈ S, l ≠ l' → ¬ Co (.inr l : P ⊕ L) (.inr l'))
    (hZ : ∀ p ∈ Z, ∀ p' ∈ Z, p ≠ p' → ¬ Co (.inl p : P ⊕ L) (.inl p')) (i j : Fin 7)
    (hT : (D7 e S Z sp zz).T i j) : (D7 e S Z sp zz).Repaired i j := by
  have H := D7_hyp e S Z sp zz hB
  by_cases h : tau7 i = tau7 j
  · exact H.repaired_of_empty hT (R7_empty S Z i j (fun hh => hh.2 h))
  · refine H.repaired_of_partial hT (fun x hx => R7_col S Z i j hx) (Iso.refl) ?_
      (R7_partial S Z hS hZ i j)
    intro x hx
    rw [M7_apply, if_neg h]
    rfl

theorem adj_hub (D : Data P L ι V U) (v : V) (u : U) (h : D.NS v u) :
    D.X.Adj (.inr (.inl v)) (.inr (.inr u)) :=
  (SimpleGraph.fromRel_adj _ _ _).2 ⟨by simp, Or.inl h⟩

variable [Fintype P] [Fintype L]

/-- The slot and degree data of the layout: injective hub placement, complete bipartite hub graph. -/
def D7_surg (hsp : ∀ v, sp v ∈ S) (hzz : ∀ v, zz v ∈ Z) (hspi : Function.Injective sp)
    (hzzi : Function.Injective zz) {q : ℕ} (hKq : K + 3 ≤ q) :
    Surg (D7 e S Z sp zz) q 3 where
  card_ι := by simp
  anti := T7_anti
  outdeg := fun i => by
    convert T7_out i using 3
    all_goals exact Iff.rfl
  arcV := fun _ i => arcV7 i
  arcV_T := fun _ i => arcV7_T i
  arcV_R := by
    intro v i
    rw [show (D7 e S Z sp zz).slotV v i = if tau7 i = true then (Sum.inr (sp v) : P ⊕ L) else Sum.inl (zz v) from rfl]
    show _ ∈ R7 S Z i (arcV7 i)
    rw [mem_R7]
    refine ⟨arcV7_T i, by rw [arcV7_tau]; cases tau7 i <;> simp, ?_⟩
    cases h : tau7 i
    · right; exact ⟨rfl, zz v, hzz v, by simp⟩
    · left; exact ⟨rfl, sp v, hsp v, by simp⟩
  arcV_inj := by
    intro v v' i h _
    have h' : (if tau7 i = true then (Sum.inr (sp v) : P ⊕ L) else Sum.inl (zz v)) =
        (if tau7 i = true then (Sum.inr (sp v') : P ⊕ L) else Sum.inl (zz v')) := h
    cases hi : tau7 i
    · rw [hi] at h'; simp at h'; exact hzzi h'
    · rw [hi] at h'; simp at h'; exact hspi h'
  arcU := fun _ i => arcU7 i
  arcU_T := fun _ i => arcU7_T i
  arcU_R := by
    intro u i
    rw [M7_symm_apply]
    rw [if_neg (by rw [arcU7_tau]; cases tau7 i <;> simp)]
    rw [show (D7 e S Z sp zz).slotU u i = if tau7 i = true then (Sum.inl (zz u) : P ⊕ L) else Sum.inr (sp u) from rfl]
    show _ ∈ R7 S Z (arcU7 i) i
    rw [mem_R7]
    refine ⟨arcU7_T i, by rw [arcU7_tau]; cases tau7 i <;> simp, ?_⟩
    cases h : tau7 i
    · left; exact ⟨by rw [arcU7_tau, h]; rfl, sp u, hsp u, by simp⟩
    · right; exact ⟨by rw [arcU7_tau, h]; rfl, zz u, hzz u, by simp⟩
  arcU_inj := by
    intro u u' i h _
    have h' : (if tau7 i = true then (Sum.inl (zz u) : P ⊕ L) else Sum.inr (sp u)) =
        (if tau7 i = true then (Sum.inl (zz u') : P ⊕ L) else Sum.inr (sp u')) := h
    cases hi : tau7 i
    · rw [hi] at h'; simp at h'; exact hspi h'
    · rw [hi] at h'; simp at h'; exact hzzi h'
  hubV := by
    intro v
    have : (univ.filter ((D7 e S Z sp zz).NS v)) = univ :=
      Finset.filter_true_of_mem (fun _ _ => trivial)
    rw [this, card_univ, Fintype.card_fin]; exact hKq
  hubU := by
    intro u
    have : (univ.filter (fun v => (D7 e S Z sp zz).NS v u)) = univ :=
      Finset.filter_true_of_mem (fun _ _ => trivial)
    rw [this, card_univ, Fintype.card_fin]; exact hKq

/-- **Corollary 10.3, formal form** (non-friendly arcs left whole, complete bipartite hub graph). For a
quadrangle of order `(q, q)` with a bijection `P ≃ L`, a set `S` of lines no two of which meet, a set `Z` of points
no two collinear, and `1 ≤ K ≤ min (|S|, |Z|, q - 3)`, there is a bipartite graph of maximum degree `q + 1 + 3`
and diameter at most `5` on `7 (|P| + |L|) + K + K` vertices. -/
theorem layout7 {q K : ℕ} (G : GQst P L q q) (e : P ≃ L) (S : Finset L) (Z : Finset P)
    (hS : ∀ l ∈ S, ∀ l' ∈ S, l ≠ l' → ¬ Co (.inr l : P ⊕ L) (.inr l'))
    (hZ : ∀ p ∈ Z, ∀ p' ∈ Z, p ≠ p' → ¬ Co (.inl p : P ⊕ L) (.inl p'))
    (hK1 : 1 ≤ K) (hKS : K ≤ S.card) (hKZ : K ≤ Z.card) (hKq : K + 3 ≤ q) :
    ∃ Y : SimpleGraph (Fin (7 * (Fintype.card P + Fintype.card L) + K + K)),
      IsBipartiteDegDiam Y (q + 1 + 3) 5 := by
  obtain ⟨s, rfl⟩ : ∃ s, q = s + 1 := ⟨q - 1, by omega⟩
  have hB := (G : GQst P L (s + 1) (s + 1)).base
  obtain ⟨spE⟩ : Nonempty (Fin K ↪ S) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hKS)
  obtain ⟨zzE⟩ : Nonempty (Fin K ↪ Z) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hKZ)
  let sp : Fin K → L := fun v => (spE v).1
  let zz : Fin K → P := fun v => (zzE v).1
  have hsp : ∀ v, sp v ∈ S := fun v => (spE v).2
  have hzz : ∀ v, zz v ∈ Z := fun v => (zzE v).2
  have hspi : Function.Injective sp := fun a b h => spE.injective (Subtype.ext h)
  have hzzi : Function.Injective zz := fun a b h => zzE.injective (Subtype.ext h)
  have H := D7_hyp e S Z sp zz hB
  have Sg := D7_surg e S Z sp zz hsp hzz hspi hzzi hKq
  haveI : Nonempty (Fin 7) := ⟨0⟩
  obtain ⟨u0⟩ : Nonempty (Fin K) := ⟨⟨0, by omega⟩⟩
  have hgV : ∀ v v' : Fin K, Reach (D7 e S Z sp zz).X (.inr (.inl v)) (.inr (.inl v')) 4 := by
    intro v v'
    have h1 := Reach.adj (adj_hub (D7 e S Z sp zz) v u0 trivial)
    have h2 := (Reach.adj (adj_hub (D7 e S Z sp zz) v' u0 trivial)).symm
    exact (h1.trans h2).mono (by norm_num)
  have hgU : ∀ u u' : Fin K, Reach (D7 e S Z sp zz).X (.inr (.inr u)) (.inr (.inr u')) 4 := by
    intro u u'
    have h1 := (Reach.adj (adj_hub (D7 e S Z sp zz) ⟨0, by omega⟩ u trivial)).symm
    have h2 := Reach.adj (adj_hub (D7 e S Z sp zz) ⟨0, by omega⟩ u' trivial)
    exact (h1.trans h2).mono (by norm_num)
  have hT' : ∀ i j, (D7 e S Z sp zz).T i j → ∀ x y : P ⊕ L,
      Reach (D7 e S Z sp zz).X (.inl (x, i)) (.inl (y, j)) 5 := fun i j hT x y =>
    H.reach_of_repaired hT (D7_repaired e S Z sp zz hB hS hZ i j hT) x y
  obtain ⟨Y, hY⟩ := H.exists_graph Sg G hT' hgV hgU
  have : (2 * 3 + 1) * (Fintype.card P + Fintype.card L) + Fintype.card (Fin K) + Fintype.card (Fin K) =
      7 * (Fintype.card P + Fintype.card L) + K + K := by simp
  rw [← this]
  exact ⟨Y, hY⟩

end Main

end BipartiteDD.LeanMaxx.D5
