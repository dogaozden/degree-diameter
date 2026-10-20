import BipartiteDD.Regular.Plus2Deg
import BipartiteDD.Regular.Match
import BipartiteDD.Regular.Defs

/-! Regularity, part 2d: the `+2` graph is `(q + 2)`-regular.

`Plus2.Frame.graph` has maximum degree `q + 2` and diameter 3. Its vertices of degree `q + 1` are exactly the
deficient points `defPt` and deficient lines `defLn` of the plane (`(q-1)(q-3)` of each, `Regular.Plus2Deg`).
A deficient point and a deficient line that are not incident can be joined by a new edge. By Hall's theorem
(`Regular.exists_matching_avoiding`) there is a perfect matching of the deficient points to the deficient lines
avoiding incident pairs, because a deficient point lies on at most `q - 4` deficient lines and vice versa
(`Plus2Geom`) and `2 (q - 4) ≤ (q - 1)(q - 3)`. Adding the matching edges makes the graph `(q + 2)`-regular;
the diameter cannot grow and the graph stays bipartite. -/

namespace BipartiteDD.Plus2

open Configuration Finset
open scoped Classical
open BipartiteDD.Regular

variable {P L : Type*} [Membership P L] [ProjectivePlane P L] [Fintype P] [Fintype L]

/-- The incidence graph of a frame is the bipartite graph of its incidence relation. -/
theorem Frame.graph_eq_biGraph (F : Frame P L) : F.graph = biGraph F.inc := by
  ext u v
  rcases u with p | l <;> rcases v with q | m <;> exact Iff.rfl

/-- There is a perfect matching of the deficient points to the deficient lines by non-incident pairs. -/
theorem Frame.exists_matching (F : Frame P L) :
    ∃ g : {p : P // F.defPt p} ≃ {l : L // F.defLn l}, ∀ p, p.1 ∉ (g p).1 := by
  have hn1 := F.card_defPt
  have hn2 := F.card_defLn
  have hc1 : Fintype.card {p : P // F.defPt p} = (univ.filter F.defPt).card := Fintype.card_subtype _
  have hc2 : Fintype.card {l : L // F.defLn l} = (univ.filter F.defLn).card := Fintype.card_subtype _
  refine exists_matching_avoiding (fun (p : {p : P // F.defPt p}) (l : {l : L // F.defLn l}) => p.1 ∉ l.1)
    (ProjectivePlane.order P L - 4) ?_ ?_
    (by omega) ?_
  · intro p
    have h := F.card_defLn_through p.2
    refine le_trans (card_le_card_of_injOn (t := univ.filter fun l : L => p.1 ∈ l ∧ F.defLn l)
      (fun l => l.1) (fun l hl => ?_) (fun a _ b _ h => Subtype.ext h)) ?_
    · simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq, not_not] at hl
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
      exact ⟨hl, l.2⟩
    · omega
  · intro l
    have h := F.card_defPt_on l.2
    refine le_trans (card_le_card_of_injOn (t := univ.filter fun p : P => p ∈ l.1 ∧ F.defPt p)
      (fun p => p.1) (fun p hp => ?_) (fun a _ b _ h => Subtype.ext h)) ?_
    · simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq, not_not] at hp
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
      exact ⟨hp, p.2⟩
    · omega
  · -- the number of deficient vertices on each side is `(q-1)(q-3) ≥ 2 (q - 4)`
    rw [hc1]
    by_cases hq : ProjectivePlane.order P L ≤ 4
    · omega
    · obtain ⟨r, hr⟩ : ∃ r, ProjectivePlane.order P L = r + 5 := ⟨ProjectivePlane.order P L - 5, by omega⟩
      rw [hr] at hn1 ⊢
      have h4 : r + 5 - 4 = r + 1 := by omega
      rw [h4]
      nlinarith

/-- The incidence relation of the frame together with the matching `g` of deficient points to deficient lines. -/
def Frame.regInc (F : Frame P L) (g : {p : P // F.defPt p} ≃ {l : L // F.defLn l}) :
    P ⊕ NewPt → L ⊕ NewLn → Prop :=
  fun v x => F.inc v x ∨ ∃ p : {p : P // F.defPt p}, v = Sum.inl p.1 ∧ x = Sum.inl (g p).1

theorem ncard_union_singleton {α : Type*} [Finite α] (S : Set α) (a : α) (ha : a ∉ S) :
    (S ∪ {a}).ncard = S.ncard + 1 := by
  rw [Set.ncard_union_eq (Set.disjoint_singleton_right.2 ha) (Set.toFinite _) (Set.toFinite _),
    Set.ncard_singleton]

/-- A matched pair is not incident in the frame structure. -/
theorem Frame.not_inc_matched (F : Frame P L) (g : {p : P // F.defPt p} ≃ {l : L // F.defLn l})
    (hg : ∀ p, p.1 ∉ (g p).1) (p : {p : P // F.defPt p}) : ¬ F.inc (Sum.inl p.1) (Sum.inl (g p).1) := by
  rw [F.inc_pp]
  rintro (⟨h, -⟩ | ⟨t, s, -, ht, -⟩)
  · exact hg p h
  · exact p.2.1 (ht ▸ F.X_mem t)

/-- After adding the matching, every vertex has degree exactly `q + 2`. -/
theorem Frame.regInc_regular (F : Frame P L) (g : {p : P // F.defPt p} ≃ {l : L // F.defLn l})
    (hg : ∀ p, p.1 ∉ (g p).1) :
    IsRegularOfDegree (biGraph (F.regInc g)) (ProjectivePlane.order P L + 2) := by
  rw [biGraph_regular_iff]
  constructor
  · intro v
    have hset : {x | F.regInc g v x} = F.ptNb v ∪ {x : L ⊕ NewLn | ∃ p : {p : P // F.defPt p}, v = Sum.inl p.1 ∧ x = Sum.inl (g p).1} :=
      Set.setOf_or
    have hdeg := F.ptNb_ncard_add v
    by_cases hv : F.defV1 v
    · rcases v with p | n
      · have hvp : F.defPt p := hv
        have hpt : {x : L ⊕ NewLn | ∃ p' : {p : P // F.defPt p}, (Sum.inl p : P ⊕ NewPt) = Sum.inl p'.1 ∧ x = Sum.inl (g p').1} =
            ({Sum.inl (g ⟨p, hvp⟩).1} : Set (L ⊕ NewLn)) := by
          ext x
          simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
          constructor
          · rintro ⟨p', h1, rfl⟩
            have : p' = ⟨p, hvp⟩ := Subtype.ext (Sum.inl_injective h1).symm
            rw [this]
          · rintro rfl
            exact ⟨⟨p, hvp⟩, rfl, rfl⟩
        rw [hset, hpt, ncard_union_singleton (F.ptNb (Sum.inl p)) _ (F.not_inc_matched g hg ⟨p, hvp⟩)]
        rw [if_pos hv] at hdeg
        exact hdeg
      · exact absurd hv (fun h => h)
    · have hpt : {x : L ⊕ NewLn | ∃ p' : {p : P // F.defPt p}, v = Sum.inl p'.1 ∧ x = Sum.inl (g p').1} = ∅ := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨p', rfl, -⟩
        exact hv p'.2
      rw [hset, hpt, Set.union_empty]
      rw [if_neg hv, add_zero] at hdeg
      exact hdeg
  · intro x
    have hset : {v | F.regInc g v x} = F.lnNb x ∪ {v : P ⊕ NewPt | ∃ p : {p : P // F.defPt p}, v = Sum.inl p.1 ∧ x = Sum.inl (g p).1} :=
      Set.setOf_or
    have hdeg := F.lnNb_ncard_add x
    by_cases hx : F.defV2 x
    · rcases x with l | n
      · have hpt : {v : P ⊕ NewPt | ∃ p' : {p : P // F.defPt p}, v = Sum.inl p'.1 ∧ (Sum.inl l : L ⊕ NewLn) = Sum.inl (g p').1} =
            ({Sum.inl (g.symm ⟨l, hx⟩).1} : Set (P ⊕ NewPt)) := by
          ext v
          simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
          constructor
          · rintro ⟨p', rfl, h2⟩
            have : g p' = ⟨l, hx⟩ := Subtype.ext (Sum.inl_injective h2).symm
            rw [← this]
            simp
          · rintro rfl
            exact ⟨g.symm ⟨l, hx⟩, rfl, by simp⟩
        have hnot : (Sum.inl (g.symm ⟨l, hx⟩).1 : P ⊕ NewPt) ∉ F.lnNb (Sum.inl l) := by
          have := F.not_inc_matched g hg (g.symm ⟨l, hx⟩)
          rw [Equiv.apply_symm_apply] at this
          exact fun h => this h
        rw [hset, hpt, ncard_union_singleton (F.lnNb (Sum.inl l)) _ hnot]
        rw [if_pos hx] at hdeg
        exact hdeg
      · exact absurd hx (fun h => h)
    · have hpt : {v : P ⊕ NewPt | ∃ p' : {p : P // F.defPt p}, v = Sum.inl p'.1 ∧ x = Sum.inl (g p').1} = ∅ := by
        ext v
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨p', -, rfl⟩
        exact hx (g p').2
      rw [hset, hpt, Set.union_empty]
      rw [if_neg hx, add_zero] at hdeg
      exact hdeg

/-- **Diameter 3, regular.** For every projective plane of order `q` with a frame there is a `(q + 2)`-regular
bipartite graph on `2 (q² + q + 6)` vertices of diameter at most `3`. -/
theorem plus2_regular {P L : Type*} [Membership P L] [ProjectivePlane P L] [Fintype P] [Fintype L]
    (F : Frame P L) :
    ∃ G : SimpleGraph (Fin (2 * (ProjectivePlane.order P L ^ 2 + ProjectivePlane.order P L + 6))),
      IsBipartiteRegDiam G (ProjectivePlane.order P L + 2) 3 := by
  obtain ⟨g, hg⟩ := F.exists_matching
  have hreg := F.regInc_regular g hg
  have hmono : F.graph ≤ biGraph (F.regInc g) := by
    rw [F.graph_eq_biGraph]
    exact biGraph_mono fun v x h => Or.inl h
  have hH : IsBipartiteRegDiam (biGraph (F.regInc g)) (ProjectivePlane.order P L + 2) 3 :=
    ⟨biGraph_colorable _, hreg, ediam_le_of_le hmono (by exact_mod_cast F.ediam_le)⟩
  have hcard : Fintype.card ((P ⊕ NewPt) ⊕ (L ⊕ NewLn)) =
      2 * (ProjectivePlane.order P L ^ 2 + ProjectivePlane.order P L + 6) := by
    have h5 : Fintype.card NewPt = 5 := rfl
    have h5' : Fintype.card NewLn = 5 := rfl
    rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_sum, h5, h5',
      ProjectivePlane.card_points P L, ProjectivePlane.card_lines P L]
    ring
  exact ⟨(biGraph (F.regInc g)).comap (Fintype.equivFinOfCardEq hcard).symm,
    hH.comap (Fintype.equivFinOfCardEq hcard)⟩

/-- The regular `+2` theorem for every projective plane of order at least `4`. -/
theorem plus2_regular_of_order {P L : Type*} [Membership P L] [ProjectivePlane P L] [Fintype P] [Fintype L]
    (h : 4 ≤ ProjectivePlane.order P L) :
    ∃ G : SimpleGraph (Fin (2 * (ProjectivePlane.order P L ^ 2 + ProjectivePlane.order P L + 6))),
      IsBipartiteRegDiam G (ProjectivePlane.order P L + 2) 3 := by
  obtain ⟨F⟩ := Frame.exists h
  exact plus2_regular F

end BipartiteDD.Plus2
