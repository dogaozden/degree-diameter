import BipartiteDD.HexagonD.Levels

/-! Theorem D, slice 2, part 8: `ForestDiam G A 4` for every vertex set `A` whose points are exactly the
singular points of `Π` and which contains every line of `S`.

Rank: points `1`, lines of `S` `0`, other lines `2`. A line not in `S` meets `Π` in a single point, a point of
`Π` lies on a single line of `S`, so each vertex has at most one lower neighbour. The root of a point is its
`S`-line, the root of a line is the `S`-line through its point in `Π`. -/

set_option linter.unusedSectionVars false

namespace BipartiteDD.HexagonD

open BipartiteDD.Hexagon BipartiteDD.Doubling Module Submodule
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [NeZero (2 : F)] {c : F}

local notation "GH" => Hexagon.incGraph (hexInc (F := F))

/-- Every line has a point in `Π`. -/
theorem exists_piPt (c : F) (l : HLine F) : ∃ p : SPt F, OnPi c p ∧ hexInc p l := by
  let f : l.1 →ₗ[F] F := (Lfun c).comp l.1.subtype
  have h1 : finrank F (LinearMap.range f) + finrank F (LinearMap.ker f) = 2 := by
    have := LinearMap.finrank_range_add_finrank_ker f
    rw [l.2.1] at this
    exact this
  have h2 : finrank F (LinearMap.range f) ≤ 1 := by
    simpa using Submodule.finrank_le (LinearMap.range f)
  have h3 : 0 < finrank F (LinearMap.ker f) := by omega
  have hne : LinearMap.ker f ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at h3
    exact lt_irrefl _ h3
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hv0' : (v : V7 F) ≠ 0 := fun h => hv0 (Subtype.ext h)
  have hvL : (v : V7 F) 0 + c * (v : V7 F) 4 = 0 := by
    simpa [f, LinearMap.mem_ker, Lfun_apply] using hv
  have hvQ : Qf (v : V7 F) = 0 := Qf_eq_zero_of_mem_hline l v.2
  refine ⟨sptOf (v : V7 F) hv0' hvQ, ?_, sptOf_mem.2 v.2⟩
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep F (v : V7 F) hv0'
  show (sptOf (v : V7 F) hv0' hvQ).1.rep 0 + c * (sptOf (v : V7 F) hv0' hvQ).1.rep 4 = 0
  have : (sptOf (v : V7 F) hv0' hvQ).1.rep = (a : F) • (v : V7 F) := by
    rw [← Units.smul_def, ha]; rfl
  rw [this]
  simp only [Pi.smul_apply, smul_eq_mul]
  linear_combination (a : F) * hvL

section

variable (c)

/-- A chosen point of `Π` on a line. -/
noncomputable def piPtPi (l : HLine F) : PtPi c :=
  ⟨(exists_piPt c l).choose, (exists_piPt c l).choose_spec.1⟩

theorem piPtPi_mem (l : HLine F) : hexInc (piPtPi c l).1 l := (exists_piPt c l).choose_spec.2

/-- Rank. -/
noncomputable def rk (c : F) : SPt F ⊕ HLine F → ℕ
  | .inl _ => 1
  | .inr l => if InPi c l then 0 else 2

/-- Root map. -/
noncomputable def root (c : F) (hc : ¬ IsSquare (-c)) : SPt F ⊕ HLine F → SPt F ⊕ HLine F
  | .inl p => if h : OnPi c p then .inr (slineOf hc ⟨p, h⟩).1 else .inl p
  | .inr l => .inr (slineOf hc (piPtPi c l)).1

end

theorem slineOf_eq_of_mem (hc : ¬ IsSquare (-c)) (p : PtPi c) {l : HLine F} (hp : hexInc p.1 l) :
    slineOf hc p = slineOf hc (piPtPi c l) := by
  by_cases hl : InPi c l
  · have h1 := (eq_slineOf_iff hc p ⟨l, hl⟩).2 hp
    have h2 := (eq_slineOf_iff hc (piPtPi c l) ⟨l, hl⟩).2 (piPtPi_mem c l)
    exact h1.symm.trans h2
  · have : p = piPtPi c l :=
      Subtype.ext (eq_of_onPi_of_not_inPi p.2 (piPtPi c l).2 hp (piPtPi_mem c l) hl)
    rw [this]

/-- Forest of depth `2`. -/
theorem forestDiam_pi (hc : ¬ IsSquare (-c)) {A : Set (SPt F ⊕ HLine F)}
    (hpts : ∀ p, Sum.inl p ∈ A ↔ OnPi c p) (hS : ∀ l, InPi c l → Sum.inr l ∈ A) :
    ForestDiam GH A 4 := by
  refine forestDiam_of_rank (rk c) (root c hc) 2 ?_ ?_ ?_ ?_
  · rintro (p | l) hx (p' | l') hy hadj
    · exact absurd hadj (by simp)
    · simp only [rk]; split_ifs <;> simp
    · simp only [rk]; split_ifs <;> simp
    · exact absurd hadj (by simp)
  · rintro (p | l) hx (p₁ | l₁) h1 (p₂ | l₂) h2 hxy hxz hy hz
    · exact absurd hxy (by simp)
    · exact absurd hxy (by simp)
    · exact absurd hxz (by simp)
    · -- `x` a point, `y`, `z` lines of lower rank, i.e. lines of `S`
      simp only [rk] at hy hz
      have hy' : InPi c l₁ := by by_contra h; simp [h] at hy
      have hz' : InPi c l₂ := by by_contra h; simp [h] at hz
      have hxy' : hexInc p l₁ := Hexagon.incGraph_adj_inl_inr.1 hxy
      have hxz' : hexInc p l₂ := Hexagon.incGraph_adj_inl_inr.1 hxz
      rw [eq_of_inPi_of_mem hc hy' hz' hxy' hxz']
    · -- `x` a line of rank `2`, `y`, `z` points
      simp only [rk] at hy hz
      have hl : ¬ InPi c l := by
        intro h; simp [h] at hy
      have hxy' : hexInc p₁ l := Hexagon.incGraph_adj_inr_inl.1 hxy
      have hxz' : hexInc p₂ l := Hexagon.incGraph_adj_inr_inl.1 hxz
      rw [eq_of_onPi_of_not_inPi ((hpts _).1 h1) ((hpts _).1 h2) hxy' hxz' hl]
    · exact absurd hxz (by simp)
    · exact absurd hxy (by simp)
    · exact absurd hxy (by simp)
  · rintro (p | l) hx (p' | l') hy hadj
    · exact absurd hadj (by simp)
    · have hp := (hpts p).1 hx
      have hpl : hexInc p l' := Hexagon.incGraph_adj_inl_inr.1 hadj
      simp only [root, hp, dite_true]
      rw [slineOf_eq_of_mem hc ⟨p, hp⟩ hpl]
    · have hp := (hpts p').1 hy
      have hpl : hexInc p' l := Hexagon.incGraph_adj_inr_inl.1 hadj
      simp only [root, hp, dite_true]
      rw [slineOf_eq_of_mem hc ⟨p', hp⟩ hpl]
    · exact absurd hadj (by simp)
  · rintro (p | l) hx
    · have hp := (hpts p).1 hx
      have hsA : Sum.inr (slineOf hc ⟨p, hp⟩).1 ∈ A := hS _ (slineOf hc ⟨p, hp⟩).2
      refine ⟨.inr (slineOf hc ⟨p, hp⟩).1, hsA, by simp [root, hp], ?_⟩
      exact ⟨SimpleGraph.Walk.cons (show ((GH).induce A).Adj ⟨.inl p, hx⟩ ⟨.inr (slineOf hc ⟨p, hp⟩).1, hsA⟩ from
        Hexagon.incGraph_adj_inl_inr.2 (mem_slineOf hc ⟨p, hp⟩)) SimpleGraph.Walk.nil, by simp⟩
    · have hqA : Sum.inl (piPtPi c l).1 ∈ A := (hpts _).2 (piPtPi c l).2
      have hsA : Sum.inr (slineOf hc (piPtPi c l)).1 ∈ A := hS _ (slineOf hc (piPtPi c l)).2
      refine ⟨.inr (slineOf hc (piPtPi c l)).1, hsA, rfl, ?_⟩
      exact ⟨SimpleGraph.Walk.cons (show ((GH).induce A).Adj ⟨.inr l, hx⟩ ⟨.inl (piPtPi c l).1, hqA⟩ from
        Hexagon.incGraph_adj_inr_inl.2 (piPtPi_mem c l))
        (SimpleGraph.Walk.cons (show ((GH).induce A).Adj ⟨.inl (piPtPi c l).1, hqA⟩
          ⟨.inr (slineOf hc (piPtPi c l)).1, hsA⟩ from
          Hexagon.incGraph_adj_inl_inr.2 (mem_slineOf hc (piPtPi c l))) SimpleGraph.Walk.nil), by simp⟩

end BipartiteDD.HexagonD
