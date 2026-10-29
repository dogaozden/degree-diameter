import BipartiteDD.LeanMaxx.D5.Base

/-! # D = 5 formalisation, part 3: level graphs with deletions and hubs (Definitions 2.1 and 3.1)

`Data P L ι V U` is the data of `research/theorems/D5_QUADRANGLE.md` Definitions 2.1 and 3.1 over the incidence
graph `I = incGraph P L` of a quadrangle (elements `P ⊕ L`, colour `col`):

* levels `ι`, arcs `T i j` (a tournament), a type `τ i : Bool` per level (the class `A_i` of level `i` is the
  set of elements of colour `τ i`, the class `B_i` that of colour `!τ i`);
* for every arc `T i j` a bijection `M i j` of `P ⊕ L` (only its restriction `A_i → B_j` matters; see `Hyp.maps`,
  `Hyp.onto`) and a set `R i j` of freed elements of `A_i`;
* hubs: `V` ("`𝓑`-hubs") take one `A`-vertex `slotV v i` in every level, `U` ("`𝓐`-hubs") one `B`-vertex
  `slotU u i`; `NS` is the hub graph `Y`.

`Data.X` is the graph `X_R^+`: level edges, the matching edges `(a, i) ~ (M i j a, j)` for `a ∈ A_i ∖ R i j`,
the hub edges, and the hub graph. With no freed elements and no hubs it is the level graph `X(T, τ, M)`. -/

namespace BipartiteDD.LeanMaxx.D5

open SimpleGraph BipartiteDD

/-- The data of a level graph with deletions and hubs. -/
structure Data (P L : Type*) [Membership P L] (ι V U : Type*) where
  T : ι → ι → Prop
  τ : ι → Bool
  M : ι → ι → (P ⊕ L) ≃ (P ⊕ L)
  R : ι → ι → Set (P ⊕ L)
  slotV : V → ι → P ⊕ L
  slotU : U → ι → P ⊕ L
  NS : V → U → Prop

/-- Vertices: level vertices `(x, i)` and hubs. -/
abbrev Vtx (P L : Type*) (ι V U : Type*) := ((P ⊕ L) × ι) ⊕ (V ⊕ U)

variable {P L : Type*} [Membership P L] {ι V U : Type*}

namespace Data

variable (D : Data P L ι V U)

/-- The directed edge relation (symmetrised by `fromRel`). -/
def rel : Vtx P L ι V U → Vtx P L ι V U → Prop
  | .inl (x, i), .inl (y, i') =>
      ((incGraph P L).Adj x y ∧ i = i') ∨ (D.T i i' ∧ col x = D.τ i ∧ x ∉ D.R i i' ∧ y = D.M i i' x)
  | .inr (.inl v), .inl (x, i) => x = D.slotV v i
  | .inr (.inr u), .inl (x, i) => x = D.slotU u i
  | .inr (.inl v), .inr (.inr u) => D.NS v u
  | _, _ => False

/-- The graph `X_R^+`. -/
def X : SimpleGraph (Vtx P L ι V U) := SimpleGraph.fromRel D.rel

/-- The hub graph `Y` on `V ⊕ U`. -/
def hubRel : V ⊕ U → V ⊕ U → Prop
  | .inl v, .inr u => D.NS v u
  | _, _ => False

/-- Level `i` of `X` is a copy of the incidence graph. -/
def lvl (i : ι) : incGraph P L →g D.X where
  toFun x := .inl (x, i)
  map_rel' := fun {x y} h => (SimpleGraph.fromRel_adj _ _ _).2
    ⟨by simpa using h.ne, Or.inl (Or.inl ⟨h, rfl⟩)⟩

theorem adj_shift {i j : ι} (hij : i ≠ j) (hT : D.T i j) {x : P ⊕ L} (hx : col x = D.τ i) (hR : x ∉ D.R i j) :
    D.X.Adj (.inl (x, i)) (.inl (D.M i j x, j)) := by
  refine (SimpleGraph.fromRel_adj _ _ _).2 ⟨?_, Or.inl (Or.inr ⟨hT, hx, hR, rfl⟩)⟩
  intro h
  exact hij (congrArg Prod.snd (Sum.inl_injective h))

theorem adj_slotV (v : V) (i : ι) : D.X.Adj (.inr (.inl v)) (.inl (D.slotV v i, i)) :=
  (SimpleGraph.fromRel_adj _ _ _).2 ⟨by simp, Or.inl rfl⟩

theorem adj_slotU (u : U) (i : ι) : D.X.Adj (.inr (.inr u)) (.inl (D.slotU u i, i)) :=
  (SimpleGraph.fromRel_adj _ _ _).2 ⟨by simp, Or.inl rfl⟩

end Data

end BipartiteDD.LeanMaxx.D5
