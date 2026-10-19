import BipartiteDD.GQST.Blowup

/-! Group GQST, part 6: stand-ins. Theorem B of `research/NOTE.md`, Section 2.

Data: points `P` with `w p` copies each, lines `L` with `m l` copies each, and a stand-in choice `σ`. For a line
copy `c = ⟨l, i⟩` and a point `p ∈ l`, `σ c p _ : Fin (w p + 1)` names the stand-in of `p` for `c`: `0` is the
original point `p`, and `k + 1` is the copy `k` of `p`.

Vertices: the point side `P ⊕ Σ p, Fin (w p)` and the line side `L ⊕ Σ l, Fin (m l)`. The graph `standin` is:
- an original line `l` is adjacent to every point-side vertex over a point of `l` (original or copy), as in `blowup`;
- a line copy `c` is adjacent to the stand-ins `standVtx p (σ c p _)` for `p ∈ c.1`, and to nothing else.

With every stand-in the original point, the graph is the copy graph `blowup`: `standin_zero_eq_blowup`. -/

namespace BipartiteDD.GQST

open SimpleGraph
open scoped Classical

variable {P L : Type*} [Membership P L]

/-- The point of a point-side vertex, forgetting which copy it is. -/
def ptOf {w : P → ℕ} : (P ⊕ Σ p, Fin (w p)) → P
  | .inl p => p
  | .inr x => x.1

/-- The point-side vertex of stand-in `j` of `p`: `0` is the original `p`, and `k + 1` is the copy `k` of `p`. -/
def standVtx {w : P → ℕ} (p : P) (j : Fin (w p + 1)) : P ⊕ Σ p, Fin (w p) :=
  if h : (j : ℕ) = 0 then .inl p else .inr ⟨p, ⟨(j : ℕ) - 1, by have := j.isLt; omega⟩⟩

theorem ptOf_standVtx {w : P → ℕ} (p : P) (j : Fin (w p + 1)) : ptOf (standVtx p j) = p := by
  unfold standVtx
  split_ifs <;> rfl

theorem standVtx_zero {w : P → ℕ} (p : P) : standVtx (w := w) p 0 = .inl p := by
  simp [standVtx]

/-- The index of a point-side vertex among the stand-ins of its point: `0` for the original, `k + 1` for copy `k`. -/
def stIdx {w : P → ℕ} : (P ⊕ Σ p, Fin (w p)) → ℕ
  | .inl _ => 0
  | .inr x => x.2.val + 1

theorem stIdx_standVtx {w : P → ℕ} (p : P) (j : Fin (w p + 1)) : stIdx (standVtx p j) = j.val := by
  unfold standVtx
  split_ifs with h
  · simp [stIdx, h]
  · simp only [stIdx]
    omega

/-- Every point-side vertex is a stand-in of its own point. -/
theorem exists_standVtx {w : P → ℕ} (q : P ⊕ Σ p, Fin (w p)) :
    ∃ (p : P) (j : Fin (w p + 1)), q = standVtx p j := by
  rcases q with p | ⟨p, i⟩
  · exact ⟨p, 0, by simp [standVtx]⟩
  · refine ⟨p, ⟨i.val + 1, by have := i.isLt; omega⟩, ?_⟩
    simp [standVtx]

variable (P L) in
/-- The relation whose symmetric closure is the stand-in graph. An original line is related to each point-side
vertex over a point on it; a line copy is related to the stand-ins of its points. -/
def standinRel {w : P → ℕ} {m : L → ℕ}
    (σ : (c : Σ l, Fin (m l)) → (p : P) → p ∈ c.1 → Fin (w p + 1)) :
    ((P ⊕ Σ p, Fin (w p)) ⊕ (L ⊕ Σ l, Fin (m l))) →
      ((P ⊕ Σ p, Fin (w p)) ⊕ (L ⊕ Σ l, Fin (m l))) → Prop
  | .inr (.inl l), .inl q => ptOf q ∈ l
  | .inr (.inr c), .inl q => ∃ (p : P) (hp : p ∈ c.1), q = standVtx p (σ c p hp)
  | _, _ => False

/-- The stand-in graph on `(P ⊕ Σ p, Fin (w p)) ⊕ (L ⊕ Σ l, Fin (m l))`. -/
def standin (P L : Type*) [Membership P L] (w : P → ℕ) (m : L → ℕ)
    (σ : (c : Σ l, Fin (m l)) → (p : P) → p ∈ c.1 → Fin (w p + 1)) :
    SimpleGraph ((P ⊕ Σ p, Fin (w p)) ⊕ (L ⊕ Σ l, Fin (m l))) :=
  SimpleGraph.fromRel (standinRel P L σ)

section Adj

variable {w : P → ℕ} {m : L → ℕ}
  {σ : (c : Σ l, Fin (m l)) → (p : P) → p ∈ c.1 → Fin (w p + 1)}

theorem standin_adj_iff {a b : (P ⊕ Σ p, Fin (w p)) ⊕ (L ⊕ Σ l, Fin (m l))} :
    (standin P L w m σ).Adj a b ↔ a ≠ b ∧ (standinRel P L σ a b ∨ standinRel P L σ b a) :=
  SimpleGraph.fromRel_adj _ _ _

/-- An original line is adjacent to a point-side vertex over one of its points. -/
theorem standin_adj_line_pt (l : L) (q : P ⊕ Σ p, Fin (w p)) (h : ptOf q ∈ l) :
    (standin P L w m σ).Adj (.inr (.inl l)) (.inl q) := by
  rw [standin_adj_iff]
  exact ⟨by simp, Or.inl h⟩

/-- A line copy is adjacent to the stand-in of each of its points. -/
theorem standin_adj_stand (c : Σ l, Fin (m l)) (p : P) (hp : p ∈ c.1) :
    (standin P L w m σ).Adj (.inr (.inr c)) (.inl (standVtx p (σ c p hp))) := by
  rw [standin_adj_iff]
  exact ⟨by simp, Or.inl ⟨p, hp, rfl⟩⟩

/-- Neighbours of a point-side vertex: original lines through its point, and the line copies it stands in for. -/
theorem standin_nbr_inl {q : P ⊕ Σ p, Fin (w p)} {y : (P ⊕ Σ p, Fin (w p)) ⊕ (L ⊕ Σ l, Fin (m l))}
    (h : (standin P L w m σ).Adj (.inl q) y) :
    (∃ l : L, y = .inr (.inl l) ∧ ptOf q ∈ l) ∨
      (∃ c : Σ l, Fin (m l), y = .inr (.inr c) ∧ ∃ (p : P) (hp : p ∈ c.1), q = standVtx p (σ c p hp)) := by
  rw [standin_adj_iff] at h
  rcases h.2 with h' | h'
  · cases y <;> exact (h' : False).elim
  · rcases y with y | l | c
    · exact (h' : False).elim
    · exact Or.inl ⟨l, rfl, h'⟩
    · exact Or.inr ⟨c, rfl, h'⟩

/-- Neighbours of an original line: point-side vertices over its points. -/
theorem standin_nbr_line {l : L} {y : (P ⊕ Σ p, Fin (w p)) ⊕ (L ⊕ Σ l, Fin (m l))}
    (h : (standin P L w m σ).Adj (.inr (.inl l)) y) : ∃ q : P ⊕ Σ p, Fin (w p), y = .inl q ∧ ptOf q ∈ l := by
  rw [standin_adj_iff] at h
  rcases h.2 with h' | h'
  · rcases y with q | l' | c
    · exact ⟨q, rfl, h'⟩
    · exact (h' : False).elim
    · exact (h' : False).elim
  · rcases y with q | l' | c
    · exact (h' : False).elim
    · exact (h' : False).elim
    · exact (h' : False).elim

/-- Neighbours of a line copy: the stand-ins of its points. -/
theorem standin_nbr_line_copy {c : Σ l, Fin (m l)}
    {y : (P ⊕ Σ p, Fin (w p)) ⊕ (L ⊕ Σ l, Fin (m l))}
    (h : (standin P L w m σ).Adj (.inr (.inr c)) y) :
    ∃ (p : P) (hp : p ∈ c.1), y = .inl (standVtx p (σ c p hp)) := by
  rw [standin_adj_iff] at h
  rcases h.2 with h' | h'
  · rcases y with q | l' | c'
    · obtain ⟨p, hp, hq⟩ := h'
      exact ⟨p, hp, congrArg Sum.inl hq⟩
    · exact (h' : False).elim
    · exact (h' : False).elim
  · rcases y with q | l' | c'
    · exact (h' : False).elim
    · exact (h' : False).elim
    · exact (h' : False).elim

end Adj

/-- The two ends of an edge of the stand-in graph lie on opposite sides. -/
theorem standinRel_isLeft {w : P → ℕ} {m : L → ℕ}
    {σ : (c : Σ l, Fin (m l)) → (p : P) → p ∈ c.1 → Fin (w p + 1)}
    {a b : (P ⊕ Σ p, Fin (w p)) ⊕ (L ⊕ Σ l, Fin (m l))} (h : standinRel P L σ a b) :
    a.isLeft ≠ b.isLeft := by
  rcases a with a | l | c <;> rcases b with b | l' | c' <;> simp [standinRel] at h ⊢

/-- The stand-in graph is bipartite: point side and line side are the two colour classes. -/
theorem standin_colorable {w : P → ℕ} {m : L → ℕ}
    (σ : (c : Σ l, Fin (m l)) → (p : P) → p ∈ c.1 → Fin (w p + 1)) :
    (standin P L w m σ).Colorable 2 := by
  refine ⟨SimpleGraph.Coloring.mk (fun v => if v.isLeft then (0 : Fin 2) else 1) ?_⟩
  intro u v h
  have hne : u.isLeft ≠ v.isLeft := by
    rw [standin_adj_iff] at h
    rcases h.2 with h' | h'
    · exact standinRel_isLeft h'
    · exact (standinRel_isLeft h').symm
  cases hu : u.isLeft <;> cases hv : v.isLeft <;> simp_all

/-- With every stand-in the original point, the stand-in graph is the copy graph `blowup`. -/
theorem standin_zero_eq_blowup {w : P → ℕ} {m : L → ℕ} :
    standin P L w m (fun _ p _ => (0 : Fin (w p + 1))) = blowup P L w m := by
  ext a b
  rw [standin_adj_iff, blowup_adj_iff]
  rcases a with (p | ⟨x, i⟩) | (l | ⟨l, k⟩) <;> rcases b with (q | ⟨y, j⟩) | (r | ⟨r, n⟩) <;>
    simp [standinRel, ptOf, under, isOrig, standVtx_zero, incGraph_adj_inl_inr, incGraph_adj_inr_inl,
      incGraph_not_adj_inl_inl, incGraph_not_adj_inr_inr]

end BipartiteDD.GQST
