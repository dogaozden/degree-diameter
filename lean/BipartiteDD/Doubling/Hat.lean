import BipartiteDD.Doubling.Core
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Girth

/-! Group Doubling, part 6: Lemma 2 (the hat lemma), "if" direction.

`ForestDiam G A r` says every component of `G[A]` is a tree of diameter at most `r`: `G[A]` is acyclic and
any two vertices in one component are at distance at most `r` in `G[A]`.

Main result `condC_of_forestDiam`: if every vertex of `G` has two distinct neighbours and every component
of `G[A]` is a tree of diameter at most `n - 2`, then condition (c) holds with `D = n`.

Proof (as in the report, with a cleaner choice of the exit vertex). Take a path `P` in `G[A]` from `x` to
`y`. A path in `G[A]` whose first vertex has no neighbour outside `A` can be extended at that end: the
first vertex has two neighbours, they all lie in `A`, and at most one of them is on the path (a second
one would close a cycle in `G[A]`). Paths in `G[A]` have length at most `n - 2`, so extending at both
ends ends with a path `Q` through `x` and `y` of length `L ≤ n - 2` whose two ends `s`, `t` each have a
neighbour `z_s`, `z_t` outside `A`. If `i`, `j` are the lengths of `Q` from `s` to `x`, `y`, then
`d(x, z_s) + d(z_s, y) ≤ i + j + 2` and `d(x, z_t) + d(z_t, y) ≤ (L - i) + (L - j) + 2`; one of these
is at most `L + 2 ≤ n`. -/

namespace BipartiteDD.Doubling

open SimpleGraph
open scoped Classical

variable {V : Type*} {G : SimpleGraph V} {A : Set V}

/-- Every component of `G[A]` is a tree of diameter at most `r`. -/
def ForestDiam (G : SimpleGraph V) (A : Set V) (r : ℕ) : Prop :=
  (G.induce A).IsAcyclic ∧ ∀ x y : A, (G.induce A).Reachable x y → (G.induce A).dist x y ≤ r

/-- If `G[A]` is acyclic, two paths of `G` inside `A` with the same ends are equal. -/
theorem eq_of_isPath_of_acyclic (hA : (G.induce A).IsAcyclic) {u v : V} {p q : G.Walk u v}
    (hp : p.IsPath) (hq : q.IsPath) (hpA : ∀ x ∈ p.support, x ∈ A) (hqA : ∀ x ∈ q.support, x ∈ A) :
    p = q := by
  have hmp := Walk.map_induce p hpA
  have hmq := Walk.map_induce q hqA
  have hinj : Function.Injective (Embedding.induce (G := G) A).toHom := fun a b hab => Subtype.ext hab
  have hp' : (p.induce A hpA).IsPath :=
    (Walk.isPath_map_iff_of_injective hinj).1 (by rw [hmp]; exact hp)
  have hq' : (q.induce A hqA).IsPath :=
    (Walk.isPath_map_iff_of_injective hinj).1 (by rw [hmq]; exact hq)
  have hsub := isAcyclic_iff_subsingleton_path.1 hA ⟨u, hpA u p.start_mem_support⟩
    ⟨v, hpA v p.end_mem_support⟩
  have h2 : p.induce A hpA = q.induce A hqA :=
    congrArg Subtype.val (hsub.elim ⟨p.induce A hpA, hp'⟩ ⟨q.induce A hqA, hq'⟩)
  have h3 := congrArg (Walk.map (Embedding.induce (G := G) A).toHom) h2
  rw [hmp, hmq] at h3
  exact h3

/-- In a graph whose components in `A` are trees of diameter at most `r`, paths inside `A` have length
at most `r`. -/
theorem length_le_of_forestDiam {r : ℕ} (hF : ForestDiam G A r) {u v : V} (p : G.Walk u v)
    (hp : p.IsPath) (hA : ∀ x ∈ p.support, x ∈ A) : p.length ≤ r := by
  have hmp := Walk.map_induce p hA
  have hinj : Function.Injective (Embedding.induce (G := G) A).toHom := fun a b hab => Subtype.ext hab
  have hp' : (p.induce A hA).IsPath :=
    (Walk.isPath_map_iff_of_injective hinj).1 (by rw [hmp]; exact hp)
  obtain ⟨q', hq', hqlen⟩ := (p.induce A hA).reachable.exists_path_of_dist
  have hsub := isAcyclic_iff_subsingleton_path.1 hF.1 ⟨u, hA u p.start_mem_support⟩
    ⟨v, hA v p.end_mem_support⟩
  have h2 : p.induce A hA = q' :=
    congrArg Subtype.val (hsub.elim ⟨p.induce A hA, hp'⟩ ⟨q', hq'⟩)
  have hlen : p.length = (p.induce A hA).length := by
    conv_lhs => rw [← hmp]
    exact Walk.length_map _ _
  rw [hlen, h2, hqlen]
  exact hF.2 _ _ (p.induce A hA).reachable

/-- A neighbour `w` of the first vertex `b` of a path in `A` that lies on the path is its second vertex,
because `G[A]` is acyclic. -/
theorem getVert_one_of_adj_mem (hA : (G.induce A).IsAcyclic) {b a : V} (R : G.Walk b a)
    (hR : R.IsPath) (hRA : ∀ x ∈ R.support, x ∈ A) {w : V} (hw : w ∈ R.support) (hbw : G.Adj b w) :
    R.getVert 1 = w := by
  have hP : (R.takeUntil w hw).IsPath := hR.takeUntil hw
  have hE : (Walk.cons hbw Walk.nil : G.Walk b w).IsPath := by simp [hbw.ne]
  have hPA : ∀ x ∈ (R.takeUntil w hw).support, x ∈ A :=
    fun x hx => hRA x (Walk.support_takeUntil_subset_support R hw hx)
  have hEA : ∀ x ∈ (Walk.cons hbw Walk.nil : G.Walk b w).support, x ∈ A := by
    intro x hx
    simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hRA _ R.start_mem_support
    · exact hRA _ hw
  have heq := eq_of_isPath_of_acyclic hA hP hE hPA hEA
  have hspec := R.take_spec hw
  calc R.getVert 1
      = ((R.takeUntil w hw).append (R.dropUntil w hw)).getVert 1 := by rw [hspec]
    _ = w := by rw [heq]; simp

/-- A path in `A` starting at `b` can be extended by a new first vertex adjacent to `b`, as there are two
neighbours of `b` and at most one is on the path. -/
theorem exists_new_nbr (hdeg : ∀ v, ∃ a b, G.Adj v a ∧ G.Adj v b ∧ a ≠ b)
    (hA : (G.induce A).IsAcyclic) {b a : V} (Q : G.Walk b a) (hQ : Q.IsPath)
    (hQA : ∀ v ∈ Q.support, v ∈ A) : ∃ w, G.Adj b w ∧ w ∉ Q.support := by
  obtain ⟨w1, w2, h1, h2, hne⟩ := hdeg b
  by_contra hall
  push Not at hall
  have e1 := getVert_one_of_adj_mem hA Q hQ hQA (hall w1 h1) h1
  have e2 := getVert_one_of_adj_mem hA Q hQ hQA (hall w2 h2) h2
  exact hne (e1.symm.trans e2)

/-- Extension at the start: a path in `A` through `x` and `y` can be extended at its first vertex until the
first vertex has a neighbour outside `A`. The measure `r - length ≤ k` bounds the number of steps. -/
theorem exists_start_ext (hdeg : ∀ v, ∃ a b, G.Adj v a ∧ G.Adj v b ∧ a ≠ b) {r : ℕ}
    (hF : ForestDiam G A r) (x y : V) :
    ∀ (k : ℕ) {b a : V} (Q : G.Walk b a), Q.IsPath → (∀ v ∈ Q.support, v ∈ A) → x ∈ Q.support →
      y ∈ Q.support → r - Q.length ≤ k →
      ∃ (b' : V) (Q' : G.Walk b' a), Q'.IsPath ∧ (∀ v ∈ Q'.support, v ∈ A) ∧ x ∈ Q'.support ∧
        y ∈ Q'.support ∧ ∃ z, z ∉ A ∧ G.Adj b' z := by
  intro k
  induction k with
  | zero =>
    intro b a Q hQ hQA hx hy hk
    by_cases hz : ∃ z, z ∉ A ∧ G.Adj b z
    · exact ⟨b, Q, hQ, hQA, hx, hy, hz⟩
    · push Not at hz
      obtain ⟨w, hbw, hw⟩ := exists_new_nbr hdeg hF.1 Q hQ hQA
      have hwA : w ∈ A := by
        by_contra h
        exact hz w h hbw
      have hQ' : (Walk.cons hbw.symm Q).IsPath := by simp [hQ, hw]
      have hQ'A : ∀ v ∈ (Walk.cons hbw.symm Q).support, v ∈ A := by
        intro v hv
        simp only [Walk.support_cons, List.mem_cons] at hv
        rcases hv with rfl | hv
        · exact hwA
        · exact hQA v hv
      have hlen := length_le_of_forestDiam hF _ hQ' hQ'A
      simp only [Walk.length_cons] at hlen
      omega
  | succ k ih =>
    intro b a Q hQ hQA hx hy hk
    by_cases hz : ∃ z, z ∉ A ∧ G.Adj b z
    · exact ⟨b, Q, hQ, hQA, hx, hy, hz⟩
    · push Not at hz
      obtain ⟨w, hbw, hw⟩ := exists_new_nbr hdeg hF.1 Q hQ hQA
      have hwA : w ∈ A := by
        by_contra h
        exact hz w h hbw
      have hQ' : (Walk.cons hbw.symm Q).IsPath := by simp [hQ, hw]
      have hQ'A : ∀ v ∈ (Walk.cons hbw.symm Q).support, v ∈ A := by
        intro v hv
        simp only [Walk.support_cons, List.mem_cons] at hv
        rcases hv with rfl | hv
        · exact hwA
        · exact hQA v hv
      refine ih (Walk.cons hbw.symm Q) hQ' hQ'A ?_ ?_ ?_
      · simp [hx]
      · simp [hy]
      · simp only [Walk.length_cons]
        omega

/-- Going from `x` to `y` through a neighbour `z` of a vertex `b` that is reachable from both. -/
theorem edist_via {x y b z : V} (p : G.Walk x b) (q : G.Walk y b) (hz : G.Adj b z) :
    G.edist x z + G.edist z y ≤ ((p.length + q.length + 2 : ℕ) : ℕ∞) := by
  have h1 : G.edist x z ≤ ((p.concat hz).length : ℕ) := edist_le _
  have h2 : G.edist z y ≤ ((Walk.cons hz.symm q.reverse).length : ℕ) := edist_le _
  calc G.edist x z + G.edist z y
      ≤ ((p.concat hz).length : ℕ∞) + ((Walk.cons hz.symm q.reverse).length : ℕ) := add_le_add h1 h2
    _ = ((p.length + q.length + 2 : ℕ) : ℕ∞) := by
        rw [Walk.length_concat, Walk.length_cons, Walk.length_reverse]
        push_cast
        ring

/-- Lemma 2, "if" direction. If every vertex of `G` has two distinct neighbours and every component of
`G[A]` is a tree of diameter at most `n - 2`, then condition (c) holds with `D = n`. -/
theorem condC_of_forestDiam (hdeg : ∀ v, ∃ a b, G.Adj v a ∧ G.Adj v b ∧ a ≠ b) {n : ℕ}
    (hn : 2 ≤ n) (hF : ForestDiam G A (n - 2)) : CondC G A n := by
  intro x y hx hy hr
  obtain ⟨P', hP', -⟩ := hr.exists_path_of_dist
  have hinj : Function.Injective (Embedding.induce (G := G) A).toHom := fun a b hab => Subtype.ext hab
  let P : G.Walk x y := P'.map (Embedding.induce (G := G) A).toHom
  have hP : P.IsPath := hP'.map hinj
  have hPA : ∀ v ∈ P.support, v ∈ A := by
    intro v hv
    obtain ⟨u, -, rfl⟩ := List.mem_map.1 (Walk.support_map _ _ ▸ hv)
    exact u.2
  obtain ⟨b₁, Q₁, hQ₁, hQ₁A, hx₁, hy₁, z₁, hz₁A, hz₁⟩ :=
    exists_start_ext hdeg hF x y (n - 2) P hP hPA P.start_mem_support P.end_mem_support
      (Nat.sub_le _ _)
  obtain ⟨b₂, Q, hQ, hQA, hxQ, hyQ, z₂, hz₂A, hz₂⟩ :=
    exists_start_ext hdeg hF x y (n - 2) Q₁.reverse hQ₁.reverse (by simpa using hQ₁A)
      (by simpa using hx₁) (by simp [hy₁]) (Nat.sub_le _ _)
  have hL := length_le_of_forestDiam hF Q hQ hQA
  have hsx := congrArg Walk.length (Q.take_spec hxQ)
  have hsy := congrArg Walk.length (Q.take_spec hyQ)
  rw [Walk.length_append] at hsx hsy
  by_cases hcase : (Q.takeUntil x hxQ).length + (Q.takeUntil y hyQ).length ≤ n - 2
  · refine ⟨z₂, hz₂A, ?_⟩
    refine (edist_via (Q.takeUntil x hxQ).reverse (Q.takeUntil y hyQ).reverse hz₂).trans ?_
    rw [Walk.length_reverse, Walk.length_reverse]
    exact_mod_cast (by omega : (Q.takeUntil x hxQ).length + (Q.takeUntil y hyQ).length + 2 ≤ n)
  · refine ⟨z₁, hz₁A, ?_⟩
    refine (edist_via (Q.dropUntil x hxQ) (Q.dropUntil y hyQ) hz₁).trans ?_
    exact_mod_cast (by omega : (Q.dropUntil x hxQ).length + (Q.dropUntil y hyQ).length + 2 ≤ n)

/-! ### Generalized polygons -/

/-- The incidence graph of a generalized `n`-gon (`n ≥ 2`), as characterised by: bipartite, girth `2n`,
diameter `n`, and every vertex of degree at least `2` (two distinct neighbours). -/
structure GenPolygonGraph (G : SimpleGraph V) (n : ℕ) : Prop where
  two_le : 2 ≤ n
  colorable : G.Colorable 2
  egirth : G.egirth = ((2 * n : ℕ) : ℕ∞)
  ediam : G.ediam = (n : ℕ∞)
  deg : ∀ v, ∃ a b, G.Adj v a ∧ G.Adj v b ∧ a ≠ b

/-- Lemma 2 ("if" direction, the one the constructions use). In the incidence graph of a generalized
`n`-gon, if every component of `G[A₀]` is a tree of diameter at most `n - 2`, then Delorme's diameter
condition (c) holds with `D = n`. -/
theorem GenPolygonGraph.condC_of_forestDiam {n : ℕ} (hG : GenPolygonGraph G n)
    (hF : ForestDiam G A (n - 2)) : CondC G A n :=
  Doubling.condC_of_forestDiam hG.deg hG.two_le hF

end BipartiteDD.Doubling
