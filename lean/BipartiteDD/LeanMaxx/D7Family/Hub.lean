import BipartiteDD.HexagonD7.Main

/-! The hub graph for the infinite diameter-7 family (research/theorems/D7_HEXAGON.md, Cor. 9.1).

A bipartite graph on `Node d m ⊕ Node d m` (line-side hubs `v`, point-side hubs `u`) with maximum degree `d + 1`
in which any two hubs of the same side are joined by a walk of length at most `6`, with `1 + d + d² + m` hubs
on each side. It is a tree: a root edge `root_V ~ root_U`; below `root_U` the `d` hubs `l1 a` (side V), below
those `l2 (a, b)` (side U), below those the `m` hubs `l3 k` (side V), whose parent in the level above is the
chosen `par k`; symmetrically below `root_V`. Every V-hub is within `3` of `root_U` and every U-hub within `3` of
`root_V`, so same-side hubs are within `6` (this is the shape of `HG(K, K; δ)` of Lemma 7.1, with a tree in place
of a plane). For `d = q - 2` and `m = 3d + 4` there are `q² + 1` hubs per side and degree `q - 1`. -/

namespace BipartiteDD.LeanMaxx.D7Family

open SimpleGraph Finset BipartiteDD.HexagonD7
open scoped Classical

/-- Hub tree nodes of one side. -/
inductive Node (d m : ℕ)
  | root : Node d m
  | l1 : Fin d → Node d m
  | l2 : Fin d × Fin d → Node d m
  | l3 : Fin m → Node d m

namespace Node

variable {d m : ℕ}

def toSum : Node d m → Unit ⊕ Fin d ⊕ (Fin d × Fin d) ⊕ Fin m
  | root => .inl ()
  | l1 a => .inr (.inl a)
  | l2 p => .inr (.inr (.inl p))
  | l3 k => .inr (.inr (.inr k))

def ofSum : Unit ⊕ Fin d ⊕ (Fin d × Fin d) ⊕ Fin m → Node d m
  | .inl () => root
  | .inr (.inl a) => l1 a
  | .inr (.inr (.inl p)) => l2 p
  | .inr (.inr (.inr k)) => l3 k

def equivSum : Node d m ≃ Unit ⊕ Fin d ⊕ (Fin d × Fin d) ⊕ Fin m where
  toFun := toSum
  invFun := ofSum
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨⟩ | a | p | k <;> rfl

noncomputable instance : Fintype (Node d m) := Fintype.ofEquiv _ equivSum.symm

theorem card_node (d m : ℕ) : Fintype.card (Node d m) = 1 + d + d * d + m := by
  rw [Fintype.card_congr equivSum]
  simp only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, Fintype.card_prod]
  ring

end Node

open Node

variable {d m : ℕ} (par : Fin m → Fin d × Fin d)

/-- The edges between a line-side hub (first argument) and a point-side hub (second argument). -/
def NS : Node d m → Node d m → Prop
  | root, root => True
  | root, l1 _ => True
  | l1 _, root => True
  | l1 a, l2 p => p.1 = a
  | l2 p, l1 a => p.1 = a
  | l2 p, l3 k => par k = p
  | l3 k, l2 p => par k = p
  | _, _ => False

theorem adjLR {v u : Node d m} (h : NS par v u) : (hubGraph (NS par)).Adj (.inl v) (.inr u) :=
  (SimpleGraph.fromRel_adj _ _ _).2 ⟨by simp, Or.inl h⟩

theorem adjRL {v u : Node d m} (h : NS par v u) : (hubGraph (NS par)).Adj (.inr u) (.inl v) :=
  (adjLR par h).symm

/-- Every line-side hub is within `3` of `root_U`. -/
theorem reachV (v : Node d m) : Reach (hubGraph (NS par)) (.inl v) (.inr root) 3 := by
  have h0 : (hubGraph (NS par)).Adj (.inl root) (.inr root) := adjLR par (by simp [NS])
  cases v with
  | root => exact (Reach.adj h0).mono (by norm_num)
  | l1 a => exact (Reach.adj (adjLR par (v := l1 a) (u := root) (by simp [NS]))).mono (by norm_num)
  | l2 p =>
    have h1 : (hubGraph (NS par)).Adj (.inl (l2 p)) (.inr (l1 p.1)) := adjLR par (by simp [NS])
    have h2 : (hubGraph (NS par)).Adj (.inr (l1 p.1)) (.inl root) := adjRL par (by simp [NS])
    exact ((Reach.adj h1).trans (Reach.adj h2)).trans (Reach.adj h0)
  | l3 k =>
    have h1 : (hubGraph (NS par)).Adj (.inl (l3 k)) (.inr (l2 (par k))) := adjLR par (by simp [NS])
    have h2 : (hubGraph (NS par)).Adj (.inr (l2 (par k))) (.inl (l1 (par k).1)) :=
      adjRL par (by simp [NS])
    have h3 : (hubGraph (NS par)).Adj (.inl (l1 (par k).1)) (.inr root) := adjLR par (by simp [NS])
    exact ((Reach.adj h1).trans (Reach.adj h2)).trans (Reach.adj h3)

/-- Every point-side hub is within `3` of `root_V`. -/
theorem reachU (u : Node d m) : Reach (hubGraph (NS par)) (.inr u) (.inl root) 3 := by
  have h0 : (hubGraph (NS par)).Adj (.inr root) (.inl root) := adjRL par (by simp [NS])
  cases u with
  | root => exact (Reach.adj h0).mono (by norm_num)
  | l1 a => exact (Reach.adj (adjRL par (v := root) (u := l1 a) (by simp [NS]))).mono (by norm_num)
  | l2 p =>
    have h1 : (hubGraph (NS par)).Adj (.inr (l2 p)) (.inl (l1 p.1)) := adjRL par (by simp [NS])
    have h2 : (hubGraph (NS par)).Adj (.inl (l1 p.1)) (.inr root) := adjLR par (by simp [NS])
    exact ((Reach.adj h1).trans (Reach.adj h2)).trans (Reach.adj h0)
  | l3 k =>
    have h1 : (hubGraph (NS par)).Adj (.inr (l3 k)) (.inl (l2 (par k))) := adjRL par (by simp [NS])
    have h2 : (hubGraph (NS par)).Adj (.inl (l2 (par k))) (.inr (l1 (par k).1)) :=
      adjLR par (by simp [NS])
    have h3 : (hubGraph (NS par)).Adj (.inr (l1 (par k).1)) (.inl root) := adjRL par (by simp [NS])
    exact ((Reach.adj h1).trans (Reach.adj h2)).trans (Reach.adj h3)

theorem reach_VV (v v' : Node d m) : Reach (hubGraph (NS par)) (.inl v) (.inl v') 6 :=
  ((reachV par v).trans (reachV par v').symm).mono (by norm_num)

theorem reach_UU (u u' : Node d m) : Reach (hubGraph (NS par)) (.inr u) (.inr u') 6 :=
  ((reachU par u).trans (reachU par u').symm).mono (by norm_num)

section Degree

set_option linter.unusedSectionVars false

variable (hfib : ∀ p, (univ.filter (fun k => par k = p)).card ≤ d)
include hfib

theorem card_root_img : (univ.image (l1 : Fin d → Node d m)).card ≤ d :=
  card_image_le.trans (by simp)

theorem card_l2_img (a : Fin d) : (univ.image (fun b : Fin d => (l2 (a, b) : Node d m))).card ≤ d :=
  card_image_le.trans (by simp)

theorem card_fiber_img (p : Fin d × Fin d) :
    ((univ.filter (fun k => par k = p)).image (l3 : Fin m → Node d m)).card ≤ d :=
  card_image_le.trans (hfib p)

theorem card_NS_left (v : Node d m) : (univ.filter (NS par v)).card ≤ d + 1 := by
  cases v with
  | root =>
    refine (card_le_card (t := insert root (univ.image (l1 : Fin d → Node d m))) ?_).trans
      ((card_insert_le _ _).trans (by have := card_root_img par hfib (m := m); omega))
    intro u hu
    simp only [mem_filter, mem_univ, true_and] at hu
    cases u <;> simp_all [NS]
  | l1 a =>
    refine (card_le_card (t := insert root (univ.image (fun b : Fin d => l2 (a, b)))) ?_).trans
      ((card_insert_le _ _).trans (by have := card_l2_img par hfib (m := m) a; omega))
    intro u hu
    simp only [mem_filter, mem_univ, true_and] at hu
    cases u with
    | root => simp
    | l1 b => simp [NS] at hu
    | l2 p =>
      simp only [NS] at hu
      simp only [mem_insert, mem_image, mem_univ, true_and, reduceCtorEq, Node.l2.injEq, false_or]
      exact ⟨p.2, by rw [← hu]⟩
    | l3 k => simp [NS] at hu
  | l2 p =>
    refine (card_le_card (t := insert (l1 p.1) ((univ.filter (fun k => par k = p)).image
        (l3 : Fin m → Node d m))) ?_).trans
      ((card_insert_le _ _).trans (by have := card_fiber_img par hfib p; omega))
    intro u hu
    simp only [mem_filter, mem_univ, true_and] at hu
    cases u with
    | root => simp [NS] at hu
    | l1 a => simp only [NS] at hu; simp [hu]
    | l2 p' => simp [NS] at hu
    | l3 k => simp only [NS] at hu; simp [hu]
  | l3 k =>
    refine (card_le_card (t := {l2 (par k)}) ?_).trans (by simp)
    intro u hu
    simp only [mem_filter, mem_univ, true_and] at hu
    cases u <;> simp_all [NS]

theorem card_NS_right (u : Node d m) : (univ.filter (fun v => NS par v u)).card ≤ d + 1 := by
  cases u with
  | root =>
    refine (card_le_card (t := insert root (univ.image (l1 : Fin d → Node d m))) ?_).trans
      ((card_insert_le _ _).trans (by have := card_root_img par hfib (m := m); omega))
    intro v hv
    simp only [mem_filter, mem_univ, true_and] at hv
    cases v <;> simp_all [NS]
  | l1 a =>
    refine (card_le_card (t := insert root (univ.image (fun b : Fin d => l2 (a, b)))) ?_).trans
      ((card_insert_le _ _).trans (by have := card_l2_img par hfib (m := m) a; omega))
    intro v hv
    simp only [mem_filter, mem_univ, true_and] at hv
    cases v with
    | root => simp
    | l1 b => simp [NS] at hv
    | l2 p =>
      simp only [NS] at hv
      simp only [mem_insert, mem_image, mem_univ, true_and, reduceCtorEq, Node.l2.injEq, false_or]
      exact ⟨p.2, by rw [← hv]⟩
    | l3 k => simp [NS] at hv
  | l2 p =>
    refine (card_le_card (t := insert (l1 p.1) ((univ.filter (fun k => par k = p)).image
        (l3 : Fin m → Node d m))) ?_).trans
      ((card_insert_le _ _).trans (by have := card_fiber_img par hfib p; omega))
    intro v hv
    simp only [mem_filter, mem_univ, true_and] at hv
    cases v with
    | root => simp [NS] at hv
    | l1 a => simp only [NS] at hv; simp [hv]
    | l2 p' => simp [NS] at hv
    | l3 k => simp only [NS] at hv; simp [hv]
  | l3 k =>
    refine (card_le_card (t := {l2 (par k)}) ?_).trans (by simp)
    intro v hv
    simp only [mem_filter, mem_univ, true_and] at hv
    cases v <;> simp_all [NS]

end Degree

/-- A parent map for the last level with fibres of size at most `d`, when `m ≤ d³`. -/
theorem exists_par {d m : ℕ} (h : m ≤ d * d * d) :
    ∃ par : Fin m → Fin d × Fin d, ∀ p, (univ.filter (fun k => par k = p)).card ≤ d := by
  obtain ⟨e⟩ : Nonempty (Fin m ↪ (Fin d × Fin d) × Fin d) :=
    Function.Embedding.nonempty_of_card_le (by simpa [Fintype.card_prod] using h)
  refine ⟨fun k => (e k).1, fun p => ?_⟩
  calc (univ.filter (fun k => (e k).1 = p)).card ≤ (univ : Finset (Fin d)).card :=
        Finset.card_le_card_of_injOn (fun k => (e k).2) (by simp) (by
          intro k hk k' hk' hkk
          simp only [coe_filter, mem_univ, true_and] at hk hk'
          exact e.injective (Prod.ext (hk.trans hk'.symm) hkk))
    _ = d := by simp

end BipartiteDD.LeanMaxx.D7Family
