import BipartiteDD.HexagonD7.Diam

/-! Diameter 7 from a generalized hexagon, part 4: bipartite, degrees, order, and the existence statement.

`exists_graph`: under `Hyp` (Theorem 1), with every point on at most `q + 1` lines and every line through at most
`q + 1` points, at most `j` hubs of each type per owner and hub-graph degrees at most `q - j`, there is a
bipartite graph of maximum degree `q + 1 + j`, diameter at most `7`, on
`(2j + 1)(|P| + |L|) + |V| + |U|` vertices. -/

namespace BipartiteDD.HexagonD7

open SimpleGraph Finset
open scoped Classical

variable {P L V U : Type*} {inc : P → L → Prop} {σ : P ≃ L} {R : Set P}
  {ownV : V → P} {ownU : U → P} {NS : V → U → Prop} {j : ℕ}

/-- The 2-colouring: points and point-type hubs `0`, lines and line-type hubs `1`. -/
def col : Vtx P L V U j → Fin 2
  | .inl (.inl _, _) => 0
  | .inl (.inr _, _) => 1
  | .inr (.inl _) => 1
  | .inr (.inr _) => 0

theorem rel_col {a b : Vtx P L V U j} (h : rel inc σ R ownV ownU NS j a b) : col a ≠ col b := by
  rcases a with ⟨x | x, i⟩ | x | x <;> rcases b with ⟨y | y, i'⟩ | y | y <;>
    first | exact absurd h id | simp [col]

theorem colorable : (X inc σ R ownV ownU NS j).Colorable 2 :=
  ⟨Coloring.mk col fun {a b} h => by
    rcases (SimpleGraph.fromRel_adj _ _ _).1 h with ⟨-, h' | h'⟩
    · exact rel_col h'
    · exact (rel_col h').symm⟩

section Degree

variable [Fintype P] [Fintype L] [Fintype V] [Fintype U] {q : ℕ}

theorem ncard_le_of_subset {W : Type*} {s : Set W} (S : Finset W) (h : s ⊆ ↑S) : s.ncard ≤ S.card := by
  rw [← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard h S.finite_toSet

theorem card_Icc_one (j : ℕ) : (Finset.Icc 1 j).card = j := by simp

theorem deg_point (hmem : ∀ v, ownV v ∈ R) (hdP : ∀ p, (univ.filter (inc p)).card ≤ q + 1)
    (hV : ∀ r, (univ.filter (fun v => ownV v = r)).card ≤ j) (p : P) (i : ZMod (2 * j + 1)) :
    ((X inc σ R ownV ownU NS j).neighborSet (.inl (.inl p, i))).ncard ≤ q + 1 + j := by
  set A : Finset (Vtx P L V U j) := (univ.filter (inc p)).image (fun l => .inl (.inr l, i))
  set B : Finset (Vtx P L V U j) := (Finset.Icc 1 j).image (fun k : ℕ => .inl (.inr (σ p), i + k))
  set C : Finset (Vtx P L V U j) := (univ.filter (fun v => ownV v = p)).image (fun v => .inr (.inl v))
  have hA : A.card ≤ q + 1 := card_image_le.trans (hdP p)
  have hB : B.card ≤ j := card_image_le.trans (card_Icc_one j).le
  have hC : C.card ≤ j := card_image_le.trans (hV p)
  have key : ∀ b, (X inc σ R ownV ownU NS j).Adj (.inl (.inl p, i)) b →
      b ∈ A ∨ (p ∉ R ∧ b ∈ B) ∨ b ∈ C := by
    intro b hb
    rcases (SimpleGraph.fromRel_adj _ _ _).1 hb with ⟨-, h | h⟩
    · rcases b with ⟨y | l, i'⟩ | y | y
      · exact absurd h id
      · rcases h with ⟨hl, rfl⟩ | ⟨hp, rfl, k, hk1, hkj, rfl⟩
        · left; exact mem_image.2 ⟨l, by simpa using hl, rfl⟩
        · right; left; exact ⟨hp, mem_image.2 ⟨k, by simp [hk1, hkj], rfl⟩⟩
      · exact absurd h id
      · exact absurd h id
    · rcases b with ⟨y | l, i'⟩ | v | u
      · exact absurd h id
      · exact absurd h id
      · have h' : p = ownV v := h
        right; right; exact mem_image.2 ⟨v, by simp [h'], rfl⟩
      · exact absurd h id
  by_cases hp : p ∈ R
  · refine (ncard_le_of_subset (A ∪ C) fun b hb => ?_).trans ((card_union_le _ _).trans (by omega))
    rcases key b hb with h | ⟨h, -⟩ | h
    · exact mem_union_left _ h
    · exact absurd hp h
    · exact mem_union_right _ h
  · refine (ncard_le_of_subset (A ∪ B) fun b hb => ?_).trans ((card_union_le _ _).trans (by omega))
    rcases key b hb with h | ⟨-, h⟩ | h
    · exact mem_union_left _ h
    · exact mem_union_right _ h
    · obtain ⟨v, hv, -⟩ := mem_image.1 h
      have hv' : ownV v = p := by simpa using hv
      exact absurd (hv' ▸ hmem v) hp


theorem deg_line (hmem : ∀ u, ownU u ∈ R) (hdL : ∀ l, (univ.filter (fun p => inc p l)).card ≤ q + 1)
    (hU : ∀ r, (univ.filter (fun u => ownU u = r)).card ≤ j) (l : L) (i' : ZMod (2 * j + 1)) :
    ((X inc σ R ownV ownU NS j).neighborSet (.inl (.inr l, i'))).ncard ≤ q + 1 + j := by
  set A : Finset (Vtx P L V U j) := (univ.filter (fun p => inc p l)).image (fun p => .inl (.inl p, i'))
  set B : Finset (Vtx P L V U j) := (Finset.Icc 1 j).image (fun k : ℕ => .inl (.inl (σ.symm l), i' - k))
  set C : Finset (Vtx P L V U j) := (univ.filter (fun u => ownU u = σ.symm l)).image (fun u => .inr (.inr u))
  have hA : A.card ≤ q + 1 := card_image_le.trans (hdL l)
  have hB : B.card ≤ j := card_image_le.trans (card_Icc_one j).le
  have hC : C.card ≤ j := card_image_le.trans (hU _)
  have key : ∀ b, (X inc σ R ownV ownU NS j).Adj (.inl (.inr l, i')) b →
      b ∈ A ∨ (σ.symm l ∉ R ∧ b ∈ B) ∨ b ∈ C := by
    intro b hb
    rcases (SimpleGraph.fromRel_adj _ _ _).1 hb with ⟨-, h | h⟩
    · rcases b with ⟨y | y, i⟩ | y | y <;> exact absurd h id
    · rcases b with ⟨p | y, i⟩ | v | u
      · rcases h with ⟨hl, rfl⟩ | ⟨hp, rfl, k, hk1, hkj, rfl⟩
        · left; exact mem_image.2 ⟨p, by simpa using hl, rfl⟩
        · right; left
          refine ⟨by simpa using hp, mem_image.2 ⟨k, by simp [hk1, hkj], by simp⟩⟩
      · exact absurd h id
      · exact absurd h id
      · have h' : l = σ (ownU u) := h
        right; right; exact mem_image.2 ⟨u, by simp [h'], rfl⟩
  by_cases hp : σ.symm l ∈ R
  · refine (ncard_le_of_subset (A ∪ C) fun b hb => ?_).trans ((card_union_le _ _).trans (by omega))
    rcases key b hb with h | ⟨h, -⟩ | h
    · exact mem_union_left _ h
    · exact absurd hp h
    · exact mem_union_right _ h
  · refine (ncard_le_of_subset (A ∪ B) fun b hb => ?_).trans ((card_union_le _ _).trans (by omega))
    rcases key b hb with h | ⟨-, h⟩ | h
    · exact mem_union_left _ h
    · exact mem_union_right _ h
    · obtain ⟨u, hu, -⟩ := mem_image.1 h
      have hu' : ownU u = σ.symm l := by simpa using hu
      exact absurd (hu' ▸ hmem u) hp

theorem deg_hubV (hNV : ∀ v, (univ.filter (NS v)).card ≤ q - j) (hjq : j ≤ q) (v : V) :
    ((X inc σ R ownV ownU NS j).neighborSet (.inr (.inl v))).ncard ≤ q + 1 + j := by
  set A : Finset (Vtx P L V U j) := univ.image (fun i : ZMod (2 * j + 1) => .inl (.inl (ownV v), i))
  set B : Finset (Vtx P L V U j) := (univ.filter (NS v)).image (fun u => .inr (.inr u))
  have hA : A.card ≤ 2 * j + 1 := card_image_le.trans (by simp [ZMod.card])
  have hB : B.card ≤ q - j := card_image_le.trans (hNV v)
  refine (ncard_le_of_subset (A ∪ B) fun b hb => ?_).trans ((card_union_le _ _).trans (by omega))
  rcases (SimpleGraph.fromRel_adj _ _ _).1 hb with ⟨-, h | h⟩
  · rcases b with ⟨p | y, i⟩ | y | u
    · have h' : p = ownV v := h
      exact mem_union_left _ (mem_image.2 ⟨i, mem_univ _, by rw [h']⟩)
    · exact absurd h id
    · exact absurd h id
    · have h' : NS v u := h
      exact mem_union_right _ (mem_image.2 ⟨u, by simpa using h', rfl⟩)
  · rcases b with ⟨y | y, i⟩ | y | y <;> exact absurd h id

theorem deg_hubU (hNU : ∀ u, (univ.filter (fun v => NS v u)).card ≤ q - j) (hjq : j ≤ q) (u : U) :
    ((X inc σ R ownV ownU NS j).neighborSet (.inr (.inr u))).ncard ≤ q + 1 + j := by
  set A : Finset (Vtx P L V U j) := univ.image (fun i : ZMod (2 * j + 1) => .inl (.inr (σ (ownU u)), i))
  set B : Finset (Vtx P L V U j) := (univ.filter (fun v => NS v u)).image (fun v => .inr (.inl v))
  have hA : A.card ≤ 2 * j + 1 := card_image_le.trans (by simp [ZMod.card])
  have hB : B.card ≤ q - j := card_image_le.trans (hNU u)
  refine (ncard_le_of_subset (A ∪ B) fun b hb => ?_).trans ((card_union_le _ _).trans (by omega))
  rcases (SimpleGraph.fromRel_adj _ _ _).1 hb with ⟨-, h | h⟩
  · rcases b with ⟨y | l, i⟩ | y | y
    · exact absurd h id
    · have h' : l = σ (ownU u) := h
      exact mem_union_left _ (mem_image.2 ⟨i, mem_univ _, by rw [h']⟩)
    · exact absurd h id
    · exact absurd h id
  · rcases b with ⟨y | y, i⟩ | v | y
    · exact absurd h id
    · exact absurd h id
    · have h' : NS v u := h
      exact mem_union_right _ (mem_image.2 ⟨v, by simpa using h', rfl⟩)
    · exact absurd h id

/-- **Theorem 1 with the order**: a bipartite graph of maximum degree `q + 1 + j` and diameter at most `7` on
`(2j + 1)(|P| + |L|) + |V| + |U|` vertices. -/
theorem exists_graph (H : Hyp inc σ R ownV ownU NS)
    (hdP : ∀ p, (univ.filter (inc p)).card ≤ q + 1) (hdL : ∀ l, (univ.filter (fun p => inc p l)).card ≤ q + 1)
    (hV : ∀ r, (univ.filter (fun v => ownV v = r)).card ≤ j)
    (hU : ∀ r, (univ.filter (fun u => ownU u = r)).card ≤ j)
    (hNV : ∀ v, (univ.filter (NS v)).card ≤ q - j) (hNU : ∀ u, (univ.filter (fun v => NS v u)).card ≤ q - j)
    (hjq : j ≤ q) :
    ∃ G : SimpleGraph (Fin ((2 * j + 1) * (Fintype.card P + Fintype.card L) + Fintype.card V +
        Fintype.card U)), IsBipartiteDegDiam G (q + 1 + j) 7 := by
  have hX : IsBipartiteDegDiam (X inc σ R ownV ownU NS j) (q + 1 + j) 7 := by
    refine ⟨colorable, fun a => ?_, H.ediam_le⟩
    rcases a with ⟨p | l, i⟩ | v | u
    · exact deg_point H.ownV_mem hdP hV p i
    · exact deg_line H.ownU_mem hdL hU l i
    · exact deg_hubV hNV hjq v
    · exact deg_hubU hNU hjq u
  have hcard : Fintype.card (Vtx P L V U j) =
      (2 * j + 1) * (Fintype.card P + Fintype.card L) + Fintype.card V + Fintype.card U := by
    simp only [Vtx, Fintype.card_sum, Fintype.card_prod, ZMod.card]; ring
  exact ⟨_, isBipartiteDegDiam_comap (Fintype.equivFinOfCardEq hcard) hX⟩

end Degree

end BipartiteDD.HexagonD7
