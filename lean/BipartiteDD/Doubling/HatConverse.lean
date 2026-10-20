import BipartiteDD.Doubling.Hat

/-! Group Doubling, part 8: Lemma 2, "only if" direction.

In the incidence graph of a generalized `n`-gon (bipartite, girth `2n`), if condition (c) holds with
`D = n` for `A`, then every component of `G[A]` is a tree of diameter at most `n - 2`.

Proof (as in the report). A path `P` of length `n - 1` inside `A` from `x` to `y` is the unique shortest
`x`-`y` walk, since two distinct paths of lengths summing to less than `2n` would close a cycle shorter
than `2n` (`path_unique_of_girth`). By parity (`G` is bipartite) any `z` with `d(x, z) + d(z, y) ≤ n`
has `d(x, z) + d(z, y) = n - 1`, so the concatenation of shortest walks is a walk of length `n - 1`, hence
equal to `P`, so `z ∈ P ⊆ A`. This contradicts `z ∉ A`. So (c) rules out paths of length `n - 1` in
`G[A]`. If a component had a cycle (of length at least `2n`) or two vertices at distance at least `n - 1`
then `G[A]` would contain such a path. -/

namespace BipartiteDD.Doubling

open SimpleGraph
open scoped Classical

variable {V : Type*} {G : SimpleGraph V} {A : Set V}

/-- In a bipartite graph, a walk's length is even iff its ends have the same colour. -/
theorem coloring_eq_iff_even (c : G.Coloring (Fin 2)) :
    ∀ {u v : V} (p : G.Walk u v), c u = c v ↔ Even p.length
  | _, _, .nil => by simp
  | u, v, .cons (v := w) h p => by
    have hne : c u ≠ c w := c.valid h
    have ih := coloring_eq_iff_even c p
    have hfin : ∀ a b d : Fin 2, a ≠ b → (a = d ↔ ¬ b = d) := by decide
    simp only [Walk.length_cons, Nat.even_add_one]
    rw [← ih]
    exact hfin _ _ _ hne

/-- Two paths with the same ends and total length less than `2n` are equal if every cycle has length at
least `2n`. -/
theorem path_unique_of_girth {n : ℕ} (hg : ∀ {a : V} (c : G.Walk a a), c.IsCycle → 2 * n ≤ c.length)
    {u v : V} {p q : G.Walk u v} (hp : p.IsPath) (hq : q.IsPath)
    (hlen : p.length + q.length < 2 * n) : p = q := by
  by_contra hne
  obtain ⟨u', v', p', q', hp', hq', hcyc⟩ := hp.exists_isCycle_of_ne hq hne
  have h1 := hg _ hcyc
  rw [Walk.length_append, Walk.length_reverse] at h1
  have h2 := Walk.length_le_of_isSubwalk hp'
  have h3 := Walk.length_le_of_isSubwalk hq'
  omega

/-- A path of length `n - 1` inside `A` rules out (c): no `z ∉ A` has `d(x, z) + d(z, y) ≤ n`. -/
theorem no_mid_of_long_path {n : ℕ} (hn : 2 ≤ n) (hcol : G.Colorable 2)
    (hg : ∀ {a : V} (c : G.Walk a a), c.IsCycle → 2 * n ≤ c.length) {x y : V} (P : G.Walk x y)
    (hP : P.IsPath) (hlen : P.length + 1 = n) (hPA : ∀ v ∈ P.support, v ∈ A) {z : V} (hz : z ∉ A) :
    ¬ (G.edist x z + G.edist z y ≤ n) := by
  intro hsum
  obtain ⟨col⟩ := hcol
  have hxz : G.edist x z ≠ ⊤ := by
    intro h
    rw [h, top_add] at hsum
    exact absurd hsum (by simp)
  have hzy : G.edist z y ≠ ⊤ := by
    intro h
    rw [h, add_top] at hsum
    exact absurd hsum (by simp)
  obtain ⟨α, hα⟩ := exists_walk_of_edist_ne_top hxz
  obtain ⟨β, hβ⟩ := exists_walk_of_edist_ne_top hzy
  set W : G.Walk x y := α.append β with hW
  have hWlen : W.length ≤ n := by
    have : ((W.length : ℕ) : ℕ∞) ≤ n := by
      rw [hW, Walk.length_append]
      push_cast
      rw [hα, hβ]
      exact hsum
    exact_mod_cast this
  -- parity: `W` and `P` have lengths of the same parity
  have hpar : Even W.length ↔ Even P.length :=
    (coloring_eq_iff_even col W).symm.trans (coloring_eq_iff_even col P)
  have hWlen' : W.length ≤ n - 1 := by
    have hpar2 : W.length % 2 = 0 ↔ P.length % 2 = 0 := by
      simpa only [Nat.even_iff] using hpar
    omega
  have hByp : W.bypass.length ≤ W.length := Walk.length_bypass_le_length W
  have hEq : P = W.bypass :=
    path_unique_of_girth hg hP W.bypass_isPath (by omega)
  have hWeq : W.bypass = W := (Walk.length_le_bypass_length_iff W).1 (by
    have : P.length = W.bypass.length := by rw [hEq]
    omega)
  have hzW : z ∈ W.support := by
    rw [hW, Walk.support_append]
    exact List.mem_append_left _ α.end_mem_support
  exact hz (hPA z (by rw [hEq, hWeq]; exact hzW))

/-- Lemma 2, "only if" direction. In the incidence graph of a generalized `n`-gon, condition (c) with
`D = n` forces every component of `G[A]` to be a tree of diameter at most `n - 2`. -/
theorem GenPolygonGraph.forestDiam_of_condC {n : ℕ} (hG : GenPolygonGraph G n) (hc : CondC G A n) :
    ForestDiam G A (n - 2) := by
  have hn := hG.two_le
  have hg : ∀ {a : V} (c : G.Walk a a), c.IsCycle → 2 * n ≤ c.length := by
    intro a c hc'
    have h1 := hc'.egirth_le_length
    rw [hG.egirth] at h1
    exact_mod_cast h1
  have hinj : Function.Injective (Embedding.induce (G := G) A).toHom :=
    fun a b hab => Subtype.ext hab
  have key : ∀ (a b : A) (P : (G.induce A).Walk a b), P.IsPath → P.length + 1 = n → False := by
    intro a b P hP hlen
    have hPm : (P.map (Embedding.induce (G := G) A).toHom).IsPath := hP.map hinj
    have hPA : ∀ v ∈ (P.map (Embedding.induce (G := G) A).toHom).support, v ∈ A := by
      intro v hv
      obtain ⟨u, -, rfl⟩ := List.mem_map.1 (Walk.support_map _ _ ▸ hv)
      exact u.2
    obtain ⟨z, hzA, hz⟩ := hc a.1 b.1 a.2 b.2 P.reachable
    exact no_mid_of_long_path hn hG.colorable hg _ hPm (by rw [Walk.length_map]; exact hlen) hPA hzA hz
  refine ⟨?_, ?_⟩
  · intro v c hcyc
    have hlen : 2 * n ≤ c.length := by
      have h1 := hg _ ((Walk.isCycle_map_iff_of_injective hinj).2 hcyc)
      rwa [Walk.length_map] at h1
    exact key _ _ (c.take (n - 1)) (hcyc.isPath_take (by omega))
      (by rw [Walk.take_length, inf_of_le_left (by omega)]; omega)
  · intro x y hr
    by_contra hlt
    push Not at hlt
    obtain ⟨r, hr', hrlen⟩ := hr.exists_path_of_dist
    exact key _ _ (r.take (n - 1)) (hr'.take _)
      (by rw [Walk.take_length, hrlen, inf_of_le_left (by omega)]; omega)

/-- Group Doubling, Lemma 2 (the hat lemma). In the incidence graph of a generalized `n`-gon, Delorme's
diameter condition (c) with `D = n` holds for `A` iff every component of `G[A]` is a tree of diameter at
most `n - 2`. -/
theorem GenPolygonGraph.condC_iff_forestDiam {n : ℕ} (hG : GenPolygonGraph G n) :
    CondC G A n ↔ ForestDiam G A (n - 2) :=
  ⟨hG.forestDiam_of_condC, hG.condC_of_forestDiam⟩

end BipartiteDD.Doubling
