import BipartiteDD.LeanAll.Route

/-! # Freed spreads (research/squads/cells/d12D7.md, section 2)

An incidence structure `(P, L, inc)` with every point-line pair within `5` and every element on two others
(`Typed.Base`), and a freed point set `F` such that every freed point `u` has a line `ℓ` with no other freed point
collinear with `u` through a line other than `ℓ` (`SpreadLike`; the points of a set of pairwise opposite lines). Then
every two elements `a, b` have a non-freed point `x` with `d(a, x) + d(x, b) ≤ 6` (`via_all`): on a shortest walk
from `a` to `b` some point is not freed, or the walk has at most two points, all freed, and a non-freed point is
found next to it.

With a duality `δ` (points to lines, lines to points, preserving incidence) as the matching of every transition and
`F` freed on every transition, this is `Route.RHyp.route` (`route_dual`); `exists_graph` is the resulting theorem for
`2j + 1` levels of type `H`. -/

namespace BipartiteDD.LeanAll.Spread

open SimpleGraph Finset BipartiteDD.Hexagon BipartiteDD.HexagonD7 BipartiteDD.LeanAll.Typed BipartiteDD.LeanAll.Route
open scoped Classical

set_option linter.unusedSectionVars false

variable {P L : Type*}

/-- Every freed point has a line through which all freed points collinear with it pass. -/
def SpreadLike (inc : P → L → Prop) (F : Set P) : Prop :=
  ∀ u ∈ F, ∃ ℓ, inc u ℓ ∧ ∀ M, inc u M → M ≠ ℓ → ∀ x, inc x M → x ≠ u → x ∉ F

/-- A non-freed point on a route of length at most `6`. -/
def Via (inc : P → L → Prop) (F : Set P) (a b : P ⊕ L) : Prop :=
  ∃ x : P, x ∉ F ∧ ∃ m n, m + n ≤ 6 ∧ Reach (Hexagon.incGraph inc) a (.inl x) m ∧
    Reach (Hexagon.incGraph inc) (.inl x) b n

variable {inc : P → L → Prop} {F : Set P}

theorem of_adj_inl {p : P} {y : P ⊕ L} (h : (Hexagon.incGraph inc).Adj (.inl p) y) : ∃ l, y = .inr l ∧ inc p l := by
  rcases y with p' | l
  · exact absurd h Hexagon.incGraph_not_adj_inl_inl
  · exact ⟨l, rfl, Hexagon.incGraph_adj_inl_inr.1 h⟩

theorem of_adj_inr {l : L} {y : P ⊕ L} (h : (Hexagon.incGraph inc).Adj (.inr l) y) : ∃ p, y = .inl p ∧ inc p l := by
  rcases y with p | l'
  · exact ⟨p, rfl, Hexagon.incGraph_adj_inr_inl.1 h⟩
  · exact absurd h Hexagon.incGraph_not_adj_inr_inr

theorem ra {p : P} {l : L} (h : inc p l) : Reach (Hexagon.incGraph inc) (.inl p) (.inr l) 1 :=
  Reach.adj (Hexagon.incGraph_adj_inl_inr.2 h)

theorem ra' {p : P} {l : L} (h : inc p l) : Reach (Hexagon.incGraph inc) (.inr l) (.inl p) 1 :=
  Reach.adj (Hexagon.incGraph_adj_inr_inl.2 h)

theorem other_line (hB : Base inc) (p : P) (ℓ : L) : ∃ M, inc p M ∧ M ≠ ℓ := by
  obtain ⟨l, l', hne, hl, hl'⟩ := hB.p2 p
  by_cases h : l = ℓ
  · exact ⟨l', hl', fun h' => hne (h.trans h'.symm)⟩
  · exact ⟨l, hl, h⟩

theorem other_on (hB : Base inc) (M : L) (p : P) : ∃ x, inc x M ∧ x ≠ p := by
  obtain ⟨y, y', hne, hy, hy'⟩ := hB.l2 M
  by_cases h : y = p
  · exact ⟨y', hy', fun h' => hne (h.trans h'.symm)⟩
  · exact ⟨y, hy, h⟩

theorem Via.symm {a b : P ⊕ L} (h : Via inc F a b) : Via inc F b a := by
  obtain ⟨x, hx, m, n, hmn, h1, h2⟩ := h
  exact ⟨x, hx, n, m, by omega, h2.symm, h1.symm⟩

/-- A freed point has a non-freed point at distance `2`. -/
theorem near_free (hB : Base inc) (hS : SpreadLike inc F) {p : P} (hp : p ∈ F) :
    ∃ x, x ∉ F ∧ Reach (Hexagon.incGraph inc) (.inl p) (.inl x) 2 := by
  obtain ⟨ℓ, -, hℓ⟩ := hS p hp
  obtain ⟨M, hM, hMℓ⟩ := other_line hB p ℓ
  obtain ⟨x, hx, hxp⟩ := other_on hB M p
  exact ⟨x, hℓ M hM hMℓ x hx hxp, (ra hM).trans (ra' hx)⟩

/-- Three freed points `p0, p, p4` with `p0, p` on `L1`, `p, p4` on `L2 ≠ L1`: impossible. -/
theorem no_mid (hS : SpreadLike inc F) {p0 p p4 : P} {L1 L2 : L} (h0 : p0 ∈ F) (h : p ∈ F) (h4 : p4 ∈ F)
    (i0 : inc p0 L1) (i1 : inc p L1) (i2 : inc p L2) (i4 : inc p4 L2) (n0 : p0 ≠ p) (n4 : p4 ≠ p)
    (nL : L1 ≠ L2) : False := by
  obtain ⟨ℓ, -, hℓ⟩ := hS p h
  have e1 : L1 = ℓ := by by_contra hc; exact hℓ L1 i1 hc p0 i0 n0 h0
  have e2 : L2 = ℓ := by by_contra hc; exact hℓ L2 i2 hc p4 i4 n4 h4
  exact nL (e1.trans e2.symm)

/-- `L0 ∋ p1`, `p1, p3 ∈ L2 ≠ L0`, `p1, p3` freed: a non-freed point on `L0`. -/
theorem end_free (hB : Base inc) (hS : SpreadLike inc F) {L0 L2 : L} {p1 p3 : P} (i01 : inc p1 L0)
    (i12 : inc p1 L2) (i23 : inc p3 L2) (nL : L0 ≠ L2) (np : p3 ≠ p1) (h1 : p1 ∈ F) (h3 : p3 ∈ F) :
    ∃ x, x ∉ F ∧ inc x L0 := by
  obtain ⟨ℓ, -, hℓ⟩ := hS p1 h1
  have e2 : L2 = ℓ := by by_contra hc; exact hℓ L2 i12 hc p3 i23 np h3
  obtain ⟨x, hx, hxp⟩ := other_on hB L0 p1
  exact ⟨x, hℓ L0 i01 (by rw [← e2]; exact nL) x hx hxp, hx⟩

theorem reach_chain {c : ℕ → P ⊕ L} {k : ℕ} (hadj : ∀ i < k, (Hexagon.incGraph inc).Adj (c i) (c (i + 1))) :
    ∀ i j, i ≤ j → j ≤ k → Reach (Hexagon.incGraph inc) (c i) (c j) (j - i) := by
  intro i j
  induction j with
  | zero =>
    intro hij _
    have : i = 0 := by omega
    subst this; exact Reach.refl _ _
  | succ j ih =>
    intro hij hjk
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · exact ((ih (by omega) (by omega)).trans (Reach.adj (hadj j (by omega)))).mono (by omega)
    · have : i = j + 1 := by omega
      subst this; exact Reach.refl _ _

/-- **The route lemma along a shortest walk** (the vertices `c 0 … c k`). -/
theorem via_chain (hB : Base inc) (hS : SpreadLike inc F) {c : ℕ → P ⊕ L} {k : ℕ} (hk : k ≤ 6)
    (hadj : ∀ i < k, (Hexagon.incGraph inc).Adj (c i) (c (i + 1))) (hinj : ∀ i, i + 2 ≤ k → c i ≠ c (i + 2)) :
    Via inc F (c 0) (c k) := by
  have hR := reach_chain hadj
  by_cases hfree : ∃ i ≤ k, ∃ x, c i = .inl x ∧ x ∉ F
  · obtain ⟨i, hi, x, hx, hxF⟩ := hfree
    refine ⟨x, hxF, i, k - i, by omega, ?_, ?_⟩
    · have := hR 0 i (by omega) hi; rw [hx] at this; simpa using this
    · have := hR i k hi le_rfl; rw [hx] at this; exact this
  push_neg at hfree
  have near : ∀ i ≤ k, ∀ p, c i = .inl p → k ≤ 2 → Via inc F (c 0) (c k) := by
    intro i hi p hp hk2
    obtain ⟨x, hxF, hpx⟩ := near_free hB hS (hfree i hi p hp)
    refine ⟨x, hxF, i + 2, (k - i) + 2, by omega, ?_, ?_⟩
    · have := hR 0 i (by omega) hi; rw [hp] at this; exact (this.trans hpx).mono (by omega)
    · have := hR i k hi le_rfl; rw [hp] at this; exact (hpx.symm.trans this).mono (by omega)
  have A : ∀ i, i < k → (Hexagon.incGraph inc).Adj (c i) (c (i + 1)) := hadj
  rcases hc0 : c 0 with p0 | L0
  · -- the walk starts at a point
    by_cases hk2 : k ≤ 2
    · have := near 0 (by omega) p0 hc0 hk2; rwa [hc0] at this
    obtain ⟨L1, e1, i01⟩ := of_adj_inl (hc0 ▸ A 0 (by omega))
    obtain ⟨p2, e2, i21⟩ := of_adj_inr (e1 ▸ A 1 (by omega))
    obtain ⟨L3, e3, i23⟩ := of_adj_inl (e2 ▸ A 2 (by omega))
    have n02 : p0 ≠ p2 := fun h => hinj 0 (by omega) (by rw [hc0, e2, h])
    have n13 : L1 ≠ L3 := fun h => hinj 1 (by omega) (by rw [e1, e3, h])
    have f0 := hfree 0 (by omega) p0 hc0
    have f2 := hfree 2 (by omega) p2 e2
    by_cases hk3 : k = 3
    · subst hk3
      obtain ⟨x, hxF, hx⟩ := end_free hB hS i23 i21 i01 n13.symm n02 f2 f0
      refine ⟨x, hxF, 4, 1, by omega, ?_, ?_⟩
      · have := hR 0 3 (by omega) le_rfl; rw [hc0, e3] at this; exact (this.trans (ra' hx)).mono (by omega)
      · rw [e3]; exact ra hx
    · obtain ⟨p4, e4, i43⟩ := of_adj_inr (e3 ▸ A 3 (by omega))
      have n24 : p2 ≠ p4 := fun h => hinj 2 (by omega) (by rw [e2, e4, h])
      exact (no_mid hS f0 f2 (hfree 4 (by omega) p4 e4) i01 i21 i23 i43 n02 (Ne.symm n24) n13).elim
  · -- the walk starts at a line
    by_cases hk0 : k = 0
    · subst hk0
      rw [hc0]
      obtain ⟨y, z, hyz, hy, hz⟩ := hB.l2 L0
      by_cases hyF : y ∉ F
      · exact ⟨y, hyF, 1, 1, by omega, ra' hy, ra hy⟩
      by_cases hzF : z ∉ F
      · exact ⟨z, hzF, 1, 1, by omega, ra' hz, ra hz⟩
      push_neg at hyF hzF
      obtain ⟨ℓ, -, hℓ⟩ := hS y hyF
      have e : L0 = ℓ := by by_contra hc; exact hℓ L0 hy hc z hz (Ne.symm hyz) hzF
      obtain ⟨M, hM, hML⟩ := other_line hB y L0
      obtain ⟨x, hx, hxy⟩ := other_on hB M y
      have hxF := hℓ M hM (by rw [← e]; exact hML) x hx hxy
      exact ⟨x, hxF, 3, 3, by omega, ((ra' hy).trans ((ra hM).trans (ra' hx))).mono (by omega),
        ((ra hx).trans ((ra' hM).trans (ra hy))).mono (by omega)⟩
    obtain ⟨p1, e1, i10⟩ := of_adj_inr (hc0 ▸ A 0 (by omega))
    by_cases hk2 : k ≤ 2
    · have := near 1 (by omega) p1 e1 hk2; rwa [hc0] at this
    obtain ⟨L2, e2, i12⟩ := of_adj_inl (e1 ▸ A 1 (by omega))
    obtain ⟨p3, e3, i32⟩ := of_adj_inr (e2 ▸ A 2 (by omega))
    have n02 : L0 ≠ L2 := fun h => hinj 0 (by omega) (by rw [hc0, e2, h])
    have n13 : p1 ≠ p3 := fun h => hinj 1 (by omega) (by rw [e1, e3, h])
    have f1 := hfree 1 (by omega) p1 e1
    have f3 := hfree 3 (by omega) p3 e3
    by_cases hk4 : k ≤ 4
    · obtain ⟨x, hxF, hx⟩ := end_free hB hS i10 i12 i32 n02 (Ne.symm n13) f1 f3
      refine ⟨x, hxF, 1, 1 + k, by omega, ra' hx, ?_⟩
      have := hR 0 k (by omega) le_rfl; rw [hc0] at this
      exact ((ra hx).trans this).mono (by omega)
    · obtain ⟨L4, e4, i34⟩ := of_adj_inl (e3 ▸ A 3 (by omega))
      obtain ⟨p5, e5, i54⟩ := of_adj_inr (e4 ▸ A 4 (by omega))
      have n24 : L2 ≠ L4 := fun h => hinj 2 (by omega) (by rw [e2, e4, h])
      have n35 : p3 ≠ p5 := fun h => hinj 3 (by omega) (by rw [e3, e5, h])
      exact (no_mid hS f1 f3 (hfree 5 (by omega) p5 e5) i12 i32 i34 i54 n13 (Ne.symm n35) n24).elim

/-- **Route lemma.** -/
theorem via_all (hB : Base inc) (hS : SpreadLike inc F) (a b : P ⊕ L) : Via inc F a b := by
  obtain ⟨w, hw⟩ := hB.all6 a b
  obtain ⟨p, hp⟩ := SimpleGraph.Reachable.exists_walk_length_eq_dist (G := Hexagon.incGraph inc) ⟨w⟩
  have hpath := p.isPath_of_length_eq_dist hp
  have hk : p.length ≤ 6 := by rw [hp]; exact (SimpleGraph.dist_le w).trans hw
  have := via_chain hB hS (c := p.getVert) hk (fun i hi => p.adj_getVert_succ hi)
    (fun i hi h => by
      have := hpath.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega) (by simp only [Set.mem_setOf_eq]; omega) h
      omega)
  rwa [p.getVert_zero, p.getVert_length] at this

/-! ## A duality as the matching -/

/-- The map of a duality on elements. -/
def dualE (φP : P ≃ L) (φL : L ≃ P) : P ⊕ L ≃ P ⊕ L := (Equiv.sumCongr φP φL).trans (Equiv.sumComm L P)

@[simp] theorem dualE_inl (φP : P ≃ L) (φL : L ≃ P) (p : P) : dualE φP φL (.inl p) = .inr (φP p) := rfl
@[simp] theorem dualE_inr (φP : P ≃ L) (φL : L ≃ P) (l : L) : dualE φP φL (.inr l) = .inl (φL l) := rfl

/-- A duality is a graph automorphism. -/
def dualIso {φP : P ≃ L} {φL : L ≃ P} (hφ : ∀ p l, inc p l ↔ inc (φL l) (φP p)) :
    Hexagon.incGraph inc ≃g Hexagon.incGraph inc where
  toEquiv := dualE φP φL
  map_rel_iff' := by
    intro a b
    rcases a with p | l <;> rcases b with p' | l'
    · simp only [Equiv.coe_fn_mk, dualE_inl]
      exact ⟨fun h => absurd h Hexagon.incGraph_not_adj_inr_inr, fun h => absurd h Hexagon.incGraph_not_adj_inl_inl⟩
    · simp only [dualE_inl, dualE_inr, Hexagon.incGraph_adj_inr_inl, Hexagon.incGraph_adj_inl_inr]
      exact (hφ p l').symm
    · simp only [dualE_inl, dualE_inr, Hexagon.incGraph_adj_inr_inl, Hexagon.incGraph_adj_inl_inr]
      exact (hφ p' l).symm
    · simp only [dualE_inr]
      exact ⟨fun h => absurd h Hexagon.incGraph_not_adj_inl_inl, fun h => absurd h Hexagon.incGraph_not_adj_inr_inr⟩

/-- The freed elements. -/
def freedE (F : Set P) : Set (P ⊕ L) := {y | ∃ p ∈ F, y = .inl p}

theorem route_dual (hB : Base inc) (hS : SpreadLike inc F) {φP : P ≃ L} {φL : L ≃ P}
    (hφ : ∀ p l, inc p l ↔ inc (φL l) (φP p)) (a b : P ⊕ L) :
    ∃ x, colE x = false ∧ x ∉ freedE (L := L) F ∧ ∃ m n, m + n ≤ 6 ∧
      Reach (Hexagon.incGraph inc) a x m ∧ Reach (Hexagon.incGraph inc) (dualE φP φL x) b n := by
  obtain ⟨x, hxF, m, n, hmn, h1, h2⟩ := via_all hB hS a ((dualE φP φL).symm b)
  refine ⟨.inl x, rfl, fun ⟨p, hp, he⟩ => hxF (Sum.inl_injective he ▸ hp), m, n, hmn, h1, ?_⟩
  have := h2.map (dualIso hφ).toHom
  simpa [dualIso] using this

/-! ## The theorem -/

variable {V U : Type*} [Fintype P] [Fintype L] [Fintype V] [Fintype U] {q j : ℕ}

/-- **Freed spread with a duality.** `2j + 1` levels of type `H`, the duality as every matching, `F` freed on every
transition, line-side hubs on freed points and point-side hubs on their images, and a hub graph `NS`: a bipartite
graph of maximum degree `q + 1 + j` and diameter at most `7` on `(2j + 1)(|P| + |L|) + |V| + |U|` vertices. -/
theorem exists_graph (hB : Base inc) (hS : SpreadLike inc F) {φP : P ≃ L} {φL : L ≃ P}
    (hφ : ∀ p l, inc p l ↔ inc (φL l) (φP p))
    (hdeg : ∀ x : P ⊕ L, (univ.filter ((Hexagon.incGraph inc).Adj x)).card ≤ q + 1)
    (slotV : V → ZMod (2 * j + 1) → P) (slotU : U → ZMod (2 * j + 1) → P) (NS : V → U → Prop)
    (hFV : ∀ v i, slotV v i ∈ F) (hFU : ∀ u i, slotU u i ∈ F)
    (hSV : ∀ i (p : P), (univ.filter (fun v => slotV v i = p)).card ≤ j)
    (hSU : ∀ i (p : P), (univ.filter (fun u => slotU u i = p)).card ≤ j)
    (r3V : ∀ v v', Reach (hubGraph NS) (.inl v) (.inl v') 6) (r3U : ∀ u u', Reach (hubGraph NS) (.inr u) (.inr u') 6)
    (hNV : ∀ v, (univ.filter (NS v)).card ≤ q - j) (hNU : ∀ u, (univ.filter (fun v => NS v u)).card ≤ q - j)
    (hjq : j ≤ q) :
    ∃ G : SimpleGraph (Fin ((2 * j + 1) * (Fintype.card P + Fintype.card L) + Fintype.card V + Fintype.card U)),
      IsBipartiteDegDiam G (q + 1 + j) 7 := by
  set δ := dualE φP φL
  have H : RHyp inc j (fun _ => false) (fun _ _ => δ) (fun _ _ => freedE F) (fun v i => .inl (slotV v i))
      (fun u i => .inr (φP (slotU u i))) NS := by
    refine ⟨hB, ?_, ?_, ?_, ?_, fun _ _ => rfl, fun _ _ => rfl, fun v v' => Or.inr (r3V v v'),
      fun u u' => Or.inr (r3U u u')⟩
    · intro i k _ _ x hx
      rcases x with p | l
      · rfl
      · simp [colE] at hx
    · intro i k _ _ y hy
      rcases y with p | l
      · simp [colE] at hy
      · show colE (δ.symm (.inr l)) = false
        have : δ.symm (.inr l) = .inl (φP.symm l) := by
          rw [Equiv.symm_apply_eq]; simp [δ]
        rw [this]; rfl
    · intro i k _ _ x ⟨p, _, he⟩
      rw [he]; rfl
    · intro i k _ _ a b
      exact route_dual hB hS hφ a b
  have hj : ∀ (x : P ⊕ L), x ∈ freedE (L := L) F →
      ((Finset.Icc 1 j).filter (fun k => x ∈ freedE (L := L) F)).card = j := by
    intro x hx
    rw [Finset.filter_true_of_mem (fun _ _ => hx)]; simp
  refine H.exists_graph hdeg (fun (i : ZMod (2 * j + 1)) (x : P ⊕ L) => ?_)
    (fun (i : ZMod (2 * j + 1)) (x : P ⊕ L) => ?_) hNV hNU hjq
  · by_cases hx : ∃ p, x = .inl p ∧ p ∈ F
    · obtain ⟨p, rfl, hp⟩ := hx
      rw [hj _ ⟨p, hp, rfl⟩]
      refine le_trans (Finset.card_le_card fun v hv => ?_) (hSV i p)
      simp only [mem_filter, mem_univ, true_and] at hv ⊢
      exact Sum.inl_injective hv
    · have : univ.filter (fun v => (Sum.inl (slotV v i) : P ⊕ L) = x) = ∅ := by
        ext v
        simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
        intro hv
        exact hx ⟨slotV v i, hv.symm, hFV v i⟩
      rw [this]; simp
  · by_cases hx : ∃ p, x = .inr (φP p) ∧ p ∈ F
    · obtain ⟨p, rfl, hp⟩ := hx
      have hδ : ∀ k : ℕ, δ.symm (.inr (φP p)) = .inl p := fun _ => by
        rw [Equiv.symm_apply_eq]; simp [δ]
      have : ((Finset.Icc 1 j).filter (fun k : ℕ => δ.symm (.inr (φP p)) ∈ freedE (L := L) F)).card = j := by
        rw [Finset.filter_true_of_mem (fun k _ => by rw [hδ k]; exact ⟨p, hp, rfl⟩)]; simp
      refine le_trans ?_ (le_of_eq this.symm)
      refine le_trans (Finset.card_le_card fun u hu => ?_) (hSU i p)
      simp only [mem_filter, mem_univ, true_and] at hu ⊢
      exact φP.injective (Sum.inr_injective hu)
    · have : univ.filter (fun u => (Sum.inr (φP (slotU u i)) : P ⊕ L) = x) = ∅ := by
        ext u
        simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
        intro hu
        exact hx ⟨slotU u i, hu.symm, hFU u i⟩
      rw [this]; simp

end BipartiteDD.LeanAll.Spread
