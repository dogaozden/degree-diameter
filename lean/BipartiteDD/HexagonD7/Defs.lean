import BipartiteDD.Hexagon.Moore
import BipartiteDD.GQ4.Main

/-! Diameter 7 from a generalized hexagon with freed points, part 1: the construction and walk helpers.

Project hexagon-family (research/projects/hexagon-family/THEOREM.md, Theorem 1). An incidence structure
`inc : P → L → Prop`, a bijection `σ : P ≃ L`, a set `R` of freed points, `m = 2j+1` levels, and hubs:
line-type hubs `V` (owner `ownV v ∈ R`, joined to `(ownV v, i)` for every level `i`), point-type hubs `U`
(joined to `(σ (ownU u), i)`), and a hub graph `NS` between `V` and `U`.

Edges of `X`: `(p,i) ~ (l,i)` for `inc p l`; the shift edges `(p,i) ~ (σ p, i+k)`, `1 ≤ k ≤ j`, for `p ∉ R`;
the hub edges. -/

namespace BipartiteDD.HexagonD7

open SimpleGraph BipartiteDD.Hexagon

section Defs

variable {P L V U : Type*} (inc : P → L → Prop) (σ : P ≃ L) (R : Set P)
  (ownV : V → P) (ownU : U → P) (NS : V → U → Prop) (j : ℕ)

/-- Vertices: level vertices `(x, i)` and hubs. -/
abbrev Vtx (P L V U : Type*) (j : ℕ) := ((P ⊕ L) × ZMod (2 * j + 1)) ⊕ (V ⊕ U)

/-- `i'` is `i` shifted forward by some `k` with `1 ≤ k ≤ j`. -/
def Shift (i i' : ZMod (2 * j + 1)) : Prop := ∃ k : ℕ, 1 ≤ k ∧ k ≤ j ∧ i' = i + k

/-- The directed edge relation (symmetrised by `fromRel`). -/
def rel : Vtx P L V U j → Vtx P L V U j → Prop
  | .inl (.inl p, i), .inl (.inr l, i') => (inc p l ∧ i = i') ∨ (p ∉ R ∧ l = σ p ∧ Shift j i i')
  | .inr (.inl v), .inl (.inl p, _) => p = ownV v
  | .inr (.inr u), .inl (.inr l, _) => l = σ (ownU u)
  | .inr (.inl v), .inr (.inr u) => NS v u
  | _, _ => False

/-- The graph `X_j(H, σ, R, NS)`. -/
def X : SimpleGraph (Vtx P L V U j) := SimpleGraph.fromRel (rel inc σ R ownV ownU NS j)

/-- The hub graph on `V ⊕ U`. -/
def hubRel : V ⊕ U → V ⊕ U → Prop
  | .inl v, .inr u => NS v u
  | _, _ => False

def hubGraph : SimpleGraph (V ⊕ U) := SimpleGraph.fromRel (hubRel NS)

/-- `r` and `p` are distinct collinear points. -/
def Coll (r p : P) : Prop := r ≠ p ∧ ∃ l, inc r l ∧ inc p l

/-- `l` and `l'` are distinct concurrent lines. -/
def Conc (l l' : L) : Prop := l ≠ l' ∧ ∃ p, inc p l ∧ inc p l'

/-- A walk of length at most `n`. -/
def Reach {W : Type*} (G : SimpleGraph W) (a b : W) (n : ℕ) : Prop := ∃ w : G.Walk a b, w.length ≤ n

end Defs

section Reach

variable {W : Type*} {G : SimpleGraph W}

theorem Reach.refl (a : W) (n : ℕ) : Reach G a a n := ⟨.nil, by simp⟩

theorem Reach.adj {a b : W} (h : G.Adj a b) : Reach G a b 1 := ⟨.cons h .nil, by simp⟩

theorem Reach.mono {a b : W} {n n' : ℕ} (h : Reach G a b n) (hn : n ≤ n') : Reach G a b n' := by
  obtain ⟨w, hw⟩ := h; exact ⟨w, hw.trans hn⟩

theorem Reach.trans {a b c : W} {n n' : ℕ} (h : Reach G a b n) (h' : Reach G b c n') :
    Reach G a c (n + n') := by
  obtain ⟨w, hw⟩ := h; obtain ⟨w', hw'⟩ := h'
  exact ⟨w.append w', by rw [Walk.length_append]; omega⟩

theorem Reach.symm {a b : W} {n : ℕ} (h : Reach G a b n) : Reach G b a n := by
  obtain ⟨w, hw⟩ := h; exact ⟨w.reverse, by simpa using hw⟩

theorem Reach.map {W' : Type*} {G' : SimpleGraph W'} (f : G →g G') {a b : W} {n : ℕ}
    (h : Reach G a b n) : Reach G' (f a) (f b) n := by
  obtain ⟨w, hw⟩ := h; exact ⟨w.map f, by simpa using hw⟩

theorem Reach.edist_le {a b : W} {n : ℕ} (h : Reach G a b n) : G.edist a b ≤ n := by
  obtain ⟨w, hw⟩ := h
  exact (SimpleGraph.edist_le w).trans (by exact_mod_cast hw)

end Reach

end BipartiteDD.HexagonD7
