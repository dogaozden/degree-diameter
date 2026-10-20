import BipartiteDD.Doubling.Hat

/-! Theorem D, slice 2, part 5: forests of bounded depth.

`forestDiam_of_rank`: let `A` be a set of vertices of `G` with a rank function `f : V → ℕ` such that along
every edge inside `A` the rank changes, and every vertex of `A` has at most one neighbour of smaller rank
in `A` (its parent). If moreover there is a root map `ρ` which is constant along edges inside `A` and joins
every vertex of `A` to `ρ x ∈ A` by a walk inside `A` of length at most `r`, then `G[A]` is a forest and
any two vertices in one component are at distance at most `2 r` (`ForestDiam G A (2 r)`). -/

namespace BipartiteDD.HexagonD

open SimpleGraph BipartiteDD.Doubling

variable {V : Type*} {G : SimpleGraph V}

/-- A graph with a rank function in which every vertex has at most one lower neighbour is acyclic. -/
theorem isAcyclic_of_rank (f : V → ℕ) (h1 : ∀ x y, G.Adj x y → f x ≠ f y)
    (h2 : ∀ x y z, G.Adj x y → G.Adj x z → f y < f x → f z < f x → y = z) : G.IsAcyclic := by
  classical
  intro u c hc
  -- the vertex of maximal rank on the cycle
  obtain ⟨m, hm', hmax'⟩ := Finset.exists_max_image c.support.toFinset f ⟨u, by simp⟩
  have hm : m ∈ c.support := by simpa using hm'
  have hmax : ∀ x ∈ c.support, f x ≤ f m := fun x hx => hmax' x (by simpa using hx)
  obtain ⟨a, b, hab, hS⟩ := Set.ncard_eq_two.1 (hc.ncard_neighborSet_toSubgraph_eq_two hm)
  have key : ∀ x, x ∈ c.toSubgraph.neighborSet m → G.Adj m x ∧ f x < f m := by
    intro x hx
    have hadj : c.toSubgraph.Adj m x := hx
    have hxs : x ∈ c.support := c.mem_verts_toSubgraph.1 hadj.snd_mem
    have hG : G.Adj m x := c.toSubgraph.adj_sub hadj
    exact ⟨hG, lt_of_le_of_ne (hmax x hxs) (h1 m x hG).symm⟩
  have ka := key a (by rw [hS]; simp)
  have kb := key b (by rw [hS]; simp)
  exact hab (h2 m a b ka.1 kb.1 ka.2 kb.2)

variable {A : Set V}

/-- The forest lemma, see the module docstring. -/
theorem forestDiam_of_rank (f : V → ℕ) (ρ : V → V) (r : ℕ)
    (h1 : ∀ x ∈ A, ∀ y ∈ A, G.Adj x y → f x ≠ f y)
    (h2 : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, G.Adj x y → G.Adj x z → f y < f x → f z < f x → y = z)
    (h3 : ∀ x ∈ A, ∀ y ∈ A, G.Adj x y → ρ x = ρ y)
    (h4 : ∀ (x : V) (hx : x ∈ A), ∃ (a : V) (ha : a ∈ A), a = ρ x ∧
      ∃ w : (G.induce A).Walk ⟨x, hx⟩ ⟨a, ha⟩, w.length ≤ r) :
    ForestDiam G A (2 * r) := by
  refine ⟨isAcyclic_of_rank (fun x : A => f x.1) (fun x y h => h1 x.1 x.2 y.1 y.2 h)
    (fun x y z hxy hxz hy hz => Subtype.ext (h2 x.1 x.2 y.1 y.2 z.1 z.2 hxy hxz hy hz)), ?_⟩
  -- the root is constant on components
  have hroot : ∀ (x y : A), (G.induce A).Walk x y → ρ x.1 = ρ y.1 := by
    intro x y w
    induction w with
    | nil => rfl
    | cons h w ih => exact (h3 _ (by simp) _ (by simp) h).trans ih
  intro x y hxy
  obtain ⟨w⟩ := hxy
  have hr := hroot x y w
  obtain ⟨a, ha, haρ, wx, hwx⟩ := h4 x.1 x.2
  obtain ⟨b, hb, hbρ, wy, hwy⟩ := h4 y.1 y.2
  have hab : a = b := haρ.trans (hr.trans hbρ.symm)
  let wy' : (G.induce A).Walk ⟨a, ha⟩ y :=
    wy.reverse.copy (Subtype.ext hab.symm) rfl
  calc (G.induce A).dist x y ≤ (wx.append wy').length := dist_le _
    _ = wx.length + wy.length := by simp [wy']
    _ ≤ 2 * r := by omega

end BipartiteDD.HexagonD
