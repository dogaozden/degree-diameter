import BipartiteDD.Doubling.Polygon

/-! Split Cayley hexagon `H(q)`, the combinatorial part: a Moore-type characterisation of generalized
hexagons.

Let `inc : P → L → Prop` be an incidence relation between finite sets of points and lines such that
every point is on `q + 1` lines, every line has `q + 1` points (`q ≥ 1`), there are
`(q + 1)(1 + q² + q⁴) = 1 + q + ⋯ + q⁵` points, and every point is joined to every line by a walk of
length at most `5` in the incidence graph. Then the incidence graph is a generalized hexagon
(`genPolygonGraph_six`): bipartite, girth `12`, diameter `6`, every vertex of degree at least `2`.

Proof (counting non-backtracking walks).
* Flag counting gives `|L| = |P| =: N`.
* From a vertex `v`, the non-backtracking walks of length `k ≥ 1` number `(q + 1) q^(k-1)`
  (`card_nbLists`; we store them as vertex lists, newest vertex first, in `nbLists`).
* Every vertex on the other side is the end of a shortest walk from `v`, of odd length at most `5`; a
  shortest walk is a path, hence non-backtracking. So the end-point map from the non-backtracking walks
  of lengths `1, 3, 5` (there are `(q + 1)(1 + q² + q⁴) = N` of them) onto the other side (`N` vertices)
  is onto, hence injective (`injOn_nbLists`).
* A cycle of length `n < 12` (so `n ∈ {4, 6, 8, 10}`) splits at a suitable odd `j` into two paths of odd
  lengths `j, n - j ≤ 5` with the same ends; injectivity makes them equal, which a cycle forbids.
  So the girth is at least `12`.
* The diameter is at most `6` (point–line at most `5` by hypothesis, the other cases via one more edge).
* From a point, the walks of lengths `0, 2, 4` reach at most `1 + (q + 1) q + (q + 1) q³ < N` points
  (`exists_far`), so some point `w` is at distance `6`; two lines through `w` give two distinct paths of
  length at most `6` between the same ends, hence a cycle of length at most `12`. -/

namespace BipartiteDD.Hexagon

open SimpleGraph Finset

/-! ### Non-backtracking walks in a regular graph -/

section NB

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- One step of extending a non-backtracking vertex list (newest vertex first, based at `v`): append a
neighbour of the newest vertex other than the previous one. -/
def nbStep (v : V) (l : List V) : Finset (List V) :=
  (univ.filter fun u => G.Adj (l.headD v) u ∧ some u ≠ l.tail.head?).image (· :: l)

/-- The non-backtracking walks of length `k` starting at `v`, as vertex lists `[x_k, …, x_1, v]`
(newest vertex first). -/
def nbLists (v : V) : ℕ → Finset (List V)
  | 0 => {[v]}
  | k + 1 => (nbLists v k).biUnion (nbStep G v)

variable {G}

theorem nbLists_zero (v : V) : nbLists G v 0 = {[v]} := rfl

theorem nbLists_succ (v : V) (k : ℕ) : nbLists G v (k + 1) = (nbLists G v k).biUnion (nbStep G v) :=
  rfl

theorem mem_nbLists_succ {v : V} {k : ℕ} {l : List V} :
    l ∈ nbLists G v (k + 1) ↔
      ∃ l' ∈ nbLists G v k, ∃ u, (G.Adj (l'.headD v) u ∧ some u ≠ l'.tail.head?) ∧ u :: l' = l := by
  simp [nbLists_succ, nbStep]

theorem length_of_mem_nbLists {v : V} :
    ∀ {k : ℕ} {l : List V}, l ∈ nbLists G v k → l.length = k + 1
  | 0, l, h => by simp [nbLists_zero] at h; simp [h]
  | k + 1, l, h => by
    obtain ⟨l', hl', u, -, rfl⟩ := mem_nbLists_succ.1 h
    simp [length_of_mem_nbLists hl']

theorem exists_of_mem_nbLists_succ {v : V} {k : ℕ} {l : List V} (h : l ∈ nbLists G v (k + 1)) :
    ∃ u x r, l = u :: x :: r ∧ G.Adj x u := by
  obtain ⟨l', hl', u, ⟨hadj, -⟩, rfl⟩ := mem_nbLists_succ.1 h
  match l', hl', hadj with
  | x :: r, _, hadj => exact ⟨u, x, r, rfl, hadj⟩
  | [], hl', _ => exact absurd (length_of_mem_nbLists hl') (by simp)

/-- In a `(q + 1)`-regular graph there are `(q + 1) q^k` non-backtracking walks of length `k + 1` from
any vertex. -/
theorem card_nbLists (q : ℕ) (hdeg : ∀ u, (univ.filter (G.Adj u)).card = q + 1) (v : V) :
    ∀ k, (nbLists G v (k + 1)).card = (q + 1) * q ^ k
  | 0 => by
    rw [nbLists_succ, nbLists_zero, singleton_biUnion, nbStep,
      card_image_of_injective _ fun _ _ h => (List.cons_eq_cons.1 h).1]
    simpa using hdeg v
  | k + 1 => by
    have hfib : ∀ l ∈ nbLists G v (k + 1), (nbStep G v l).card = q := by
      intro l hl
      obtain ⟨u, x, r, rfl, hxu⟩ := exists_of_mem_nbLists_succ hl
      rw [nbStep, card_image_of_injective _ fun _ _ h => (List.cons_eq_cons.1 h).1]
      have : (univ.filter fun w => G.Adj ((u :: x :: r).headD v) w ∧
          some w ≠ (u :: x :: r).tail.head?) = (univ.filter (G.Adj u)).erase x := by
        ext w
        simp only [List.headD_cons, List.tail_cons, List.head?_cons, mem_filter, mem_univ, true_and,
          mem_erase, ne_eq, Option.some.injEq]
        tauto
      rw [this, card_erase_of_mem (by simpa using hxu.symm), hdeg]
      simp
    have hdisj : (↑(nbLists G v (k + 1)) : Set (List V)).PairwiseDisjoint (nbStep G v) := by
      intro l _ l' _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro a ha ha'
      simp only [nbStep, mem_image] at ha ha'
      obtain ⟨u, -, rfl⟩ := ha
      obtain ⟨u', -, h⟩ := ha'
      exact hne (List.cons_eq_cons.1 h).2.symm
    rw [nbLists_succ, card_biUnion hdisj, sum_congr rfl hfib, sum_const, smul_eq_mul,
      card_nbLists q hdeg v k]
    ring

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem support_headD {u w : V} (p : G.Walk u w) (d : V) : p.support.headD d = u := by
  cases p <;> rfl

/-- The support of a path ending at `v`, read from its start, is a non-backtracking list based at
`v`. -/
theorem support_mem_nbLists {v : V} :
    ∀ {w : V} (p : G.Walk w v), p.IsPath → p.support ∈ nbLists G v p.length
  | _, .nil, _ => by simp [nbLists_zero]
  | _, .cons h p, hp => by
    rw [Walk.cons_isPath_iff] at hp
    rw [Walk.support_cons, Walk.length_cons, mem_nbLists_succ]
    refine ⟨p.support, support_mem_nbLists p hp.1, _, ⟨?_, ?_⟩, rfl⟩
    · rw [support_headD]; exact h.symm
    · intro he
      exact hp.2 (List.mem_of_mem_tail (List.mem_of_mem_head? he.symm))

/-- **Moore-type injectivity.** In a `(q + 1)`-regular graph, if the ends of the non-backtracking walks
of lengths `1, 3, 5` from `v` cover a set of at least `(q + 1)(1 + q² + q⁴)` vertices, then different
such walks have different ends. -/
theorem injOn_nbLists (q : ℕ) (hdeg : ∀ u, (univ.filter (G.Adj u)).card = q + 1) (v : V)
    (T : Finset V) (hT : (q + 1) * (1 + q ^ 2 + q ^ 4) ≤ T.card)
    (hreach : ∀ w ∈ T, ∃ l ∈ nbLists G v 1 ∪ nbLists G v 3 ∪ nbLists G v 5, l.headD v = w) :
    Set.InjOn (fun l : List V => l.headD v)
      (↑(nbLists G v 1 ∪ nbLists G v 3 ∪ nbLists G v 5) : Set (List V)) := by
  have h1 : (nbLists G v 1).card = q + 1 := by simpa using card_nbLists q hdeg v 0
  have h3 := card_nbLists q hdeg v 2
  have h5 := card_nbLists q hdeg v 4
  have hX : (nbLists G v 1 ∪ nbLists G v 3 ∪ nbLists G v 5).card ≤ (q + 1) * (1 + q ^ 2 + q ^ 4) :=
    calc _ ≤ (nbLists G v 1 ∪ nbLists G v 3).card + (nbLists G v 5).card := card_union_le _ _
      _ ≤ (nbLists G v 1).card + (nbLists G v 3).card + (nbLists G v 5).card :=
          Nat.add_le_add_right (card_union_le _ _) _
      _ = (q + 1) * (1 + q ^ 2 + q ^ 4) := by rw [h1, h3, h5]; ring
  have hsub : T ⊆ (nbLists G v 1 ∪ nbLists G v 3 ∪ nbLists G v 5).image (fun l => l.headD v) := by
    intro w hw
    obtain ⟨l, hl, rfl⟩ := hreach w hw
    exact mem_image_of_mem _ hl
  have := card_le_card hsub
  exact card_image_iff.1 (le_antisymm card_image_le (by omega))

/-- In a `(q + 1)`-regular graph with `q ≥ 1`, in any set of at least `(q + 1)(1 + q² + q⁴)` vertices
some vertex is not the end of a non-backtracking walk of length `0`, `2` or `4` from `v`. -/
theorem exists_far (q : ℕ) (hq : 1 ≤ q) (hdeg : ∀ u, (univ.filter (G.Adj u)).card = q + 1) (v : V)
    (T : Finset V) (hT : (q + 1) * (1 + q ^ 2 + q ^ 4) ≤ T.card) :
    ∃ w ∈ T, ∀ l ∈ nbLists G v 0 ∪ nbLists G v 2 ∪ nbLists G v 4, l.headD v ≠ w := by
  have h0 : (nbLists G v 0).card = 1 := by simp [nbLists_zero]
  have h2 := card_nbLists q hdeg v 1
  have h4 := card_nbLists q hdeg v 3
  have hq5 : 0 < q ^ 5 := pow_pos (by omega) 5
  have hexp : (q + 1) * (1 + q ^ 2 + q ^ 4) = 1 + (q + 1) * q ^ 1 + (q + 1) * q ^ 3 + q ^ 5 := by
    ring
  have hX : ((nbLists G v 0 ∪ nbLists G v 2 ∪ nbLists G v 4).image fun l => l.headD v).card <
      T.card :=
    calc _ ≤ (nbLists G v 0 ∪ nbLists G v 2 ∪ nbLists G v 4).card := card_image_le
      _ ≤ (nbLists G v 0 ∪ nbLists G v 2).card + (nbLists G v 4).card := card_union_le _ _
      _ ≤ (nbLists G v 0).card + (nbLists G v 2).card + (nbLists G v 4).card :=
          Nat.add_le_add_right (card_union_le _ _) _
      _ = (q + 1) * (1 + q ^ 2 + q ^ 4) - q ^ 5 := by
          rw [h0, h2, h4]
          omega
      _ < T.card := by omega
  obtain ⟨w, hwT, hw⟩ := exists_mem_notMem_of_card_lt_card hX
  exact ⟨w, hwT, fun l hl he => hw (he ▸ mem_image_of_mem _ hl)⟩

end NB

/-! ### Incidence graphs -/

section Inc

variable {P L : Type*} (inc : P → L → Prop)

/-- The incidence graph of an incidence structure: points `Sum.inl p` and lines `Sum.inr l`, with `p`
adjacent to `l` iff `inc p l`. -/
def incGraph : SimpleGraph (P ⊕ L) where
  Adj a b := match a, b with
    | .inl p, .inr l => inc p l
    | .inr l, .inl p => inc p l
    | _, _ => False
  symm := ⟨fun a b h => by cases a <;> cases b <;> exact h⟩
  loopless := ⟨fun a h => by cases a <;> exact h⟩

variable {inc}

@[simp] theorem incGraph_adj_inl_inr {p : P} {l : L} :
    (incGraph inc).Adj (.inl p) (.inr l) ↔ inc p l := Iff.rfl

@[simp] theorem incGraph_adj_inr_inl {p : P} {l : L} :
    (incGraph inc).Adj (.inr l) (.inl p) ↔ inc p l := Iff.rfl

@[simp] theorem incGraph_not_adj_inl_inl {p p' : P} : ¬ (incGraph inc).Adj (.inl p) (.inl p') :=
  id

@[simp] theorem incGraph_not_adj_inr_inr {l l' : L} : ¬ (incGraph inc).Adj (.inr l) (.inr l') :=
  id

theorem incGraph_adj_isLeft {a b : P ⊕ L} (h : (incGraph inc).Adj a b) : a.isLeft ≠ b.isLeft := by
  cases a <;> cases b <;> simp_all

/-- In the incidence graph a walk has even length iff its ends are on the same side. -/
theorem isLeft_eq_iff_even : ∀ {a b : P ⊕ L} (p : (incGraph inc).Walk a b),
    a.isLeft = b.isLeft ↔ Even p.length
  | _, _, .nil => by simp
  | _, _, .cons h p => by
    have hne := incGraph_adj_isLeft h
    have ih := isLeft_eq_iff_even p
    have hfin : ∀ a b d : Bool, a ≠ b → (a = d ↔ ¬ b = d) := by decide
    rw [Walk.length_cons, Nat.even_add_one, ← ih]
    exact hfin _ _ _ hne

/-- The incidence graph is bipartite. -/
theorem incGraph_colorable : (incGraph inc).Colorable 2 :=
  ⟨Coloring.mk (fun v => if v.isLeft then (0 : Fin 2) else 1) fun {a b} h => by
    have := incGraph_adj_isLeft h
    cases a <;> cases b <;> simp_all⟩

open scoped Classical

theorem card_filter_adj_inl [Fintype P] [Fintype L] (p : P) :
    (univ.filter ((incGraph inc).Adj (.inl p))).card = (univ.filter (inc p)).card := by
  rw [show univ.filter ((incGraph inc).Adj (.inl p)) =
      (univ.filter (inc p)).map Function.Embedding.inr by
    ext x; rcases x with p' | l <;> simp, card_map]

theorem card_filter_adj_inr [Fintype P] [Fintype L] (l : L) :
    (univ.filter ((incGraph inc).Adj (.inr l))).card = (univ.filter (fun p => inc p l)).card := by
  rw [show univ.filter ((incGraph inc).Adj (.inr l)) =
      (univ.filter (fun p => inc p l)).map Function.Embedding.inl by
    ext x; rcases x with p | l' <;> simp, card_map]

/-- Flag counting: if every point is on `k` lines and every line has `k` points (`k ≥ 1`), there are as
many lines as points. -/
theorem card_lines_eq [Fintype P] [Fintype L] {k : ℕ} (hk : 1 ≤ k)
    (hP : ∀ p, Nat.card {l // inc p l} = k) (hL : ∀ l, Nat.card {p // inc p l} = k) :
    Nat.card L = Nat.card P := by
  have hP' : ∀ p, (univ.filter (inc p)).card = k := fun p => by
    rw [← hP p, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hL' : ∀ l, (univ.filter (fun p => inc p l)).card = k := fun l => by
    rw [← hL l, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h : ∑ p : P, ∑ l : L, (if inc p l then 1 else 0) =
      ∑ l : L, ∑ p : P, (if inc p l then 1 else 0) := sum_comm
  simp only [← card_filter, hP', hL', sum_const, card_univ, smul_eq_mul] at h
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact (Nat.eq_of_mul_eq_mul_right hk h).symm

theorem edist_le_of_walk {V : Type*} {G : SimpleGraph V} {u w : V} (W : G.Walk u w) {n : ℕ}
    (h : W.length ≤ n) : G.edist u w ≤ n :=
  (Walk.edist_le W).trans (by exact_mod_cast h)

variable [Fintype P] [Fintype L]

/-- A walk of length at most `5` between the two sides yields a non-backtracking list of length `1`,
`3` or `5` based at its end. -/
theorem exists_odd_nbList {w v : P ⊕ L} (W : (incGraph inc).Walk w v) (hW : W.length ≤ 5)
    (hs : w.isLeft ≠ v.isLeft) :
    ∃ l ∈ nbLists (incGraph inc) v 1 ∪ nbLists (incGraph inc) v 3 ∪ nbLists (incGraph inc) v 5,
      l.headD v = w := by
  have hl := support_mem_nbLists W.bypass W.bypass_isPath
  have hlen : W.bypass.length ≤ 5 := (W.length_bypass_le_length).trans hW
  have hodd : ¬ Even W.bypass.length := fun he => hs ((isLeft_eq_iff_even _).2 he)
  rw [Nat.not_even_iff_odd, Nat.odd_iff] at hodd
  refine ⟨W.bypass.support, ?_, support_headD _ _⟩
  rcases (by omega : W.bypass.length = 1 ∨ W.bypass.length = 3 ∨ W.bypass.length = 5)
    with h | h | h <;> rw [h] at hl <;> simp [hl]

/-- A walk of length at most `5` inside one side yields a non-backtracking list of length `0`, `2` or
`4` based at its end. -/
theorem exists_even_nbList {w v : P ⊕ L} (W : (incGraph inc).Walk w v) (hW : W.length ≤ 5)
    (hs : w.isLeft = v.isLeft) :
    ∃ l ∈ nbLists (incGraph inc) v 0 ∪ nbLists (incGraph inc) v 2 ∪ nbLists (incGraph inc) v 4,
      l.headD v = w := by
  have hl := support_mem_nbLists W.bypass W.bypass_isPath
  have hlen : W.bypass.length ≤ 5 := (W.length_bypass_le_length).trans hW
  have hev : Even W.bypass.length := (isLeft_eq_iff_even _).1 hs
  rw [Nat.even_iff] at hev
  refine ⟨W.bypass.support, ?_, support_headD _ _⟩
  rcases (by omega : W.bypass.length = 0 ∨ W.bypass.length = 2 ∨ W.bypass.length = 4)
    with h | h | h <;> rw [h] at hl <;> simp [hl]

theorem mem_odd_union {v : P ⊕ L} {k : ℕ} {l : List (P ⊕ L)} (hk : k ≤ 5) (hodd : k % 2 = 1)
    (hl : l ∈ nbLists (incGraph inc) v k) :
    l ∈ nbLists (incGraph inc) v 1 ∪ nbLists (incGraph inc) v 3 ∪ nbLists (incGraph inc) v 5 := by
  rcases (by omega : k = 1 ∨ k = 3 ∨ k = 5) with rfl | rfl | rfl <;> simp [hl]

variable (inc) in
/-- **Moore-type theorem for generalized hexagons.** Let `inc` be an incidence relation between finite
sets of points `P` and lines `L` with every point on `q + 1` lines and every line through `q + 1` points
(`q ≥ 1`), with `(q + 1)(1 + q² + q⁴)` points, and such that every point is joined to every line by a
walk of length at most `5` in the incidence graph. Then the incidence graph is the incidence graph of a
generalized hexagon: bipartite, girth `12`, diameter `6`, every vertex of degree at least `2`. -/
theorem genPolygonGraph_six (q : ℕ) (hq : 1 ≤ q)
    (hP : ∀ p, Nat.card {l // inc p l} = q + 1) (hL : ∀ l, Nat.card {p // inc p l} = q + 1)
    (hN : Nat.card P = (q + 1) * (1 + q ^ 2 + q ^ 4))
    (hd : ∀ p l, ∃ w : (incGraph inc).Walk (.inl p) (.inr l), w.length ≤ 5) :
    Doubling.GenPolygonGraph (incGraph inc) 6 := by
  have hP' : ∀ p, (univ.filter (inc p)).card = q + 1 := fun p => by
    rw [← hP p, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hL' : ∀ l, (univ.filter (fun p => inc p l)).card = q + 1 := fun l => by
    rw [← hL l, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hcP : Fintype.card P = (q + 1) * (1 + q ^ 2 + q ^ 4) := by rw [← hN, Nat.card_eq_fintype_card]
  have hcL : Fintype.card L = (q + 1) * (1 + q ^ 2 + q ^ 4) := by
    rw [← hN, ← card_lines_eq (by omega : 1 ≤ q + 1) hP hL, Nat.card_eq_fintype_card]
  have hdeg : ∀ u, (univ.filter ((incGraph inc).Adj u)).card = q + 1 := by
    rintro (p | l)
    · rw [card_filter_adj_inl, hP']
    · rw [card_filter_adj_inr, hL']
  -- injectivity of the end-point map, from every base vertex
  have hinj : ∀ v : P ⊕ L, Set.InjOn (fun l : List (P ⊕ L) => l.headD v)
      (↑(nbLists (incGraph inc) v 1 ∪ nbLists (incGraph inc) v 3 ∪ nbLists (incGraph inc) v 5) : Set (List (P ⊕ L))) := by
    rintro (p | l)
    · refine injOn_nbLists q hdeg _ (univ.map Function.Embedding.inr) (by simp [hcL]) ?_
      intro w hw
      obtain ⟨l, -, rfl⟩ := mem_map.1 hw
      obtain ⟨W, hW⟩ := hd p l
      exact exists_odd_nbList (w := .inr l) W.reverse (by simpa using hW) (by simp)
    · refine injOn_nbLists q hdeg _ (univ.map Function.Embedding.inl) (by simp [hcP]) ?_
      intro w hw
      obtain ⟨p, -, rfl⟩ := mem_map.1 hw
      obtain ⟨W, hW⟩ := hd p l
      exact exists_odd_nbList (w := .inl p) W hW (by simp)
  -- girth at least 12
  have hgirth : ∀ (a : P ⊕ L) (c : (incGraph inc).Walk a a), c.IsCycle → 12 ≤ c.length := by
    intro a c hc
    by_contra hlt
    push Not at hlt
    obtain ⟨m, hm⟩ := (isLeft_eq_iff_even c).1 rfl
    have h3 := hc.three_le_length
    set n := c.length with hn
    set j := n / 2 - 1 + n / 2 % 2 with hj
    have hjn : j < n := by omega
    have hα := support_mem_nbLists _ (hc.isPath_take hjn).reverse
    have hβ := support_mem_nbLists _ (hc.isPath_drop (n := j) (by omega))
    rw [Walk.length_reverse, Walk.take_length, ← hn, min_eq_left hjn.le] at hα
    rw [Walk.drop_length, ← hn] at hβ
    have heq := hinj a (mem_odd_union (by omega) (by omega) hα)
      (mem_odd_union (by omega) (by omega) hβ) (by simp only [support_headD])
    have hαβ : (c.take j).reverse = c.drop j := Walk.ext_support heq
    have hce := congrArg Walk.edges (c.append_take_drop_eq j)
    rw [Walk.edges_append, ← hαβ, Walk.edges_reverse] at hce
    have hdisj := List.disjoint_of_nodup_append (hce ▸ hc.edges_nodup)
    obtain ⟨e, he⟩ : ∃ e, e ∈ (c.take j).edges := by
      apply List.exists_mem_of_ne_nil
      intro h0
      have := congrArg List.length h0
      rw [Walk.length_edges, Walk.take_length, ← hn, min_eq_left hjn.le] at this
      simp at this
      omega
    exact hdisj he (List.mem_reverse.2 he)
  -- diameter at most 6
  have hdiam : ∀ u w : P ⊕ L, (incGraph inc).edist u w ≤ 6 := by
    have hline : ∀ p : P, ∃ l, inc p l := fun p => by
      obtain ⟨l, hl⟩ := card_pos.1 (by rw [hP']; omega : 0 < (univ.filter (inc p)).card)
      exact ⟨l, (mem_filter.1 hl).2⟩
    have hpt : ∀ l : L, ∃ p, inc p l := fun l => by
      obtain ⟨p, hp⟩ := card_pos.1 (by rw [hL']; omega : 0 < (univ.filter (fun p => inc p l)).card)
      exact ⟨p, (mem_filter.1 hp).2⟩
    rintro (p | l) (p' | l')
    · obtain ⟨l, hl⟩ := hline p'
      obtain ⟨W, hW⟩ := hd p l
      exact edist_le_of_walk (n := 6) (W.concat (show (incGraph inc).Adj (.inr l) (.inl p') from hl))
        (by rw [Walk.length_concat]; omega)
    · obtain ⟨W, hW⟩ := hd p l'
      exact edist_le_of_walk (n := 6) W (by omega)
    · obtain ⟨W, hW⟩ := hd p' l
      exact edist_le_of_walk (n := 6) W.reverse (by rw [Walk.length_reverse]; omega)
    · obtain ⟨p', hp'⟩ := hpt l'
      obtain ⟨W, hW⟩ := hd p' l
      exact edist_le_of_walk (n := 6) (W.reverse.concat (show (incGraph inc).Adj (.inl p') (.inr l') from hp'))
        (by rw [Walk.length_concat, Walk.length_reverse]; omega)
  -- a point at distance 6 from a fixed point
  have hPne : Nonempty P := Fintype.card_pos_iff.1 (by rw [hcP]; positivity)
  obtain ⟨p₀⟩ := hPne
  obtain ⟨w, hwT, hwfar⟩ := exists_far q hq hdeg (.inl p₀) (univ.map Function.Embedding.inl)
    (by simp [hcP])
  obtain ⟨p₁, -, rfl⟩ := mem_map.1 hwT
  have hfar : ∀ W : (incGraph inc).Walk (.inl p₁) (.inl p₀), 6 ≤ W.length := by
    intro W
    by_contra hlt
    push Not at hlt
    obtain ⟨l, hl, he⟩ := exists_even_nbList W (by omega) rfl
    exact hwfar l hl he
  refine ⟨by norm_num, incGraph_colorable, ?_, ?_, ?_⟩
  · -- girth exactly 12
    refine le_antisymm ?_ (le_egirth.2 fun a c hc => by exact_mod_cast hgirth a c hc)
    obtain ⟨l₁, hl₁, l₂, hl₂, hne⟩ := one_lt_card.1 (by rw [hP']; omega : 1 < (univ.filter (inc p₁)).card)
    rw [mem_filter] at hl₁ hl₂
    have mk : ∀ l, inc p₁ l → ∃ γ : (incGraph inc).Walk (.inl p₁) (.inl p₀),
        γ.IsPath ∧ γ.length ≤ 6 ∧ γ.getVert 1 = .inr l := by
      intro l hl
      obtain ⟨W, hW⟩ := hd p₀ l
      refine ⟨.cons (show (incGraph inc).Adj (.inl p₁) (.inr l) from hl) W.bypass.reverse, ?_, ?_, by simp⟩
      · rw [Walk.cons_isPath_iff]
        refine ⟨W.bypass_isPath.reverse, fun hmem => ?_⟩
        have h1 := hfar (W.bypass.reverse.dropUntil _ hmem)
        have h2 := W.bypass.reverse.length_dropUntil_le_length hmem
        have h3 := W.length_bypass_le_length
        rw [Walk.length_reverse] at h2
        omega
      · have h3 := W.length_bypass_le_length
        rw [Walk.length_cons, Walk.length_reverse]
        omega
    obtain ⟨γ₁, hγ₁, hlen₁, hv₁⟩ := mk l₁ hl₁.2
    obtain ⟨γ₂, hγ₂, hlen₂, hv₂⟩ := mk l₂ hl₂.2
    have hγ : γ₁ ≠ γ₂ := fun h => hne (Sum.inr_injective (hv₁.symm.trans (h ▸ hv₂)))
    obtain ⟨_, -, -, c, hc, hclen⟩ := hγ₁.exists_isCycle_length_le_add_of_ne hγ₂ hγ
    exact hc.egirth_le_length.trans (by exact_mod_cast (by omega : c.length ≤ 2 * 6))
  · -- diameter exactly 6
    refine le_antisymm (ediam_le_iff.2 fun u w => by exact_mod_cast hdiam u w) ?_
    refine le_trans ?_ (edist_le_ediam (u := .inl p₁) (v := .inl p₀))
    have hne : (incGraph inc).edist (.inl p₁) (.inl p₀) ≠ ⊤ := ne_top_of_le_ne_top (by simp) (hdiam _ _)
    obtain ⟨W, hW⟩ := exists_walk_of_edist_ne_top hne
    rw [← hW]
    exact_mod_cast hfar W
  · -- two distinct neighbours
    intro u
    obtain ⟨a, ha, b, hb, hab⟩ :=
      one_lt_card.1 (by rw [hdeg]; omega : 1 < (univ.filter ((incGraph inc).Adj u)).card)
    exact ⟨a, b, (mem_filter.1 ha).2, (mem_filter.1 hb).2, hab⟩

end Inc

-- #print axioms BipartiteDD.Hexagon.genPolygonGraph_six
-- [propext, Classical.choice, Quot.sound]

end BipartiteDD.Hexagon
