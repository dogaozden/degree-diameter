import BipartiteDD.HexagonD.PiCount
import BipartiteDD.HexagonD.Polygon

/-! Theorem D, slice 2, part 4 (target 1): `S` is a spread of `Π ∩ Q`.

For a finite field `F` of odd characteristic and `c ∈ F` with `-c` a non-square, `S = SLine c` is the set of
`H(q)`-lines contained in `Π : x₀ + c x₄ = 0`.
* `existsUnique_sline`: every singular point of `Π` lies on exactly one line of `S`;
* `sline_opp`, `sline_edist`: two distinct lines of `S` are opposite, i.e. at distance `6` in the
  incidence graph (`edist = 6`);
* `card_sline`: `|S| = q³ + 1`. -/

namespace BipartiteDD.HexagonD

open BipartiteDD.Hexagon Module Submodule

variable {F : Type*} [Field F] [Fintype F] [NeZero (2 : F)] {c : F}

noncomputable instance fintypeHLine : Fintype (HLine F) :=
  haveI := finite_hline (F := F); Fintype.ofFinite _

noncomputable instance fintypeSLine (c : F) : Fintype (SLine c) := Fintype.ofFinite _

theorem rep_not_mem_span_of_ne {p p' : Projectivization F (V7 F)} (h : p ≠ p') :
    p'.rep ∉ span F {p.rep} := by
  intro hmem
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
  apply h
  symm
  rw [← Projectivization.mk_rep p', ← Projectivization.mk_rep p, Projectivization.mk_eq_mk_iff']
  exact ⟨a, ha⟩

/-- The `S`-line through a singular point of `Π`. -/
noncomputable def slineOf (hc : ¬ IsSquare (-c)) (p : PtPi c) : SLine c :=
  (exists_sline hc p.1.1.rep_nonzero p.1.2 p.2).choose

theorem mem_slineOf (hc : ¬ IsSquare (-c)) (p : PtPi c) : p.1.1.rep ∈ (slineOf hc p).1.1 :=
  (exists_sline hc p.1.1.rep_nonzero p.1.2 p.2).choose_spec

theorem eq_slineOf_iff (hc : ¬ IsSquare (-c)) (p : PtPi c) (s : SLine c) :
    s = slineOf hc p ↔ p.1.1.rep ∈ s.1.1 :=
  ⟨fun h => h ▸ mem_slineOf hc p, fun h =>
    sline_unique hc p.1.1.rep_nonzero p.1.2 p.2 h (mem_slineOf hc p)⟩

/-- Every singular point of `Π` lies on exactly one line of `S`. -/
theorem existsUnique_sline (hc : ¬ IsSquare (-c)) (p : SPt F) (hp : p.1.rep 0 + c * p.1.rep 4 = 0) :
    ∃! s : SLine c, p.1.rep ∈ s.1.1 :=
  ⟨slineOf hc ⟨p, hp⟩, mem_slineOf hc ⟨p, hp⟩, fun s hs =>
    (eq_slineOf_iff hc ⟨p, hp⟩ s).2 hs⟩

/-- Distinct lines of `S` are far apart: no point of one is collinear with a point of the other. -/
theorem sline_opp (hc : ¬ IsSquare (-c)) {s s' : SLine c} (hne : s ≠ s') :
    Opp (hexInc (F := F)) s.1 s'.1 := by
  rintro ⟨p, M, p', h1, h2, h3, h4⟩
  have h1' : p.1.rep ∈ s.1.1 := h1
  have h2' : p.1.rep ∈ M.1 := h2
  have h3' : p'.1.rep ∈ M.1 := h3
  have h4' : p'.1.rep ∈ s'.1.1 := h4
  have hpL : p.1.rep 0 + c * p.1.rep 4 = 0 := s.2 _ h1'
  have hp'L : p'.1.rep 0 + c * p'.1.rep 4 = 0 := s'.2 _ h4'
  by_cases hpp : p = p'
  · subst hpp
    exact hne (sline_unique hc p.1.rep_nonzero p.2 hpL h1' h4')
  · have hMspan : M.1 = span F {p.1.rep, p'.1.rep} :=
      hline_eq_span M h2' h3' p.1.rep_nonzero (rep_not_mem_span_of_ne (fun h => hpp (Subtype.ext h)))
    have hM : InPi c M := by
      intro x hx
      rw [hMspan] at hx
      obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hx
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination a * hpL + b * hp'L
    have e1 := sline_unique hc p.1.rep_nonzero p.2 hpL (s := ⟨M, hM⟩) (s' := s) h2' h1'
    have e2 := sline_unique hc p'.1.rep_nonzero p'.2 hp'L (s := ⟨M, hM⟩) (s' := s') h3' h4'
    exact hne (e1.symm.trans e2)

/-- Distinct lines of `S` are opposite: they are at distance `6` in the incidence graph of `H(q)`. -/
theorem sline_edist (hc : ¬ IsSquare (-c)) {s s' : SLine c} (hne : s ≠ s') :
    (Hexagon.incGraph (hexInc (F := F))).edist (.inr s.1) (.inr s'.1) = 6 :=
  edist_eq_six_of_opp genPolygonGraph_hexagon (sline_opp hc hne)

/-- Number of points of an `S`-line: all of its points are singular points of `Π`. -/
theorem card_sline [DecidableEq F] (hc : ¬ IsSquare (-c)) :
    Fintype.card (SLine c) = Fintype.card F ^ 3 + 1 := by
  classical
  have hfib : ∀ s : SLine c, Fintype.card {p : PtPi c // slineOf hc p = s} =
      Fintype.card F + 1 := by
    intro s
    have e : {p : PtPi c // slineOf hc p = s} ≃ {p : SPt F // p.1.rep ∈ s.1.1} :=
      { toFun := fun p => ⟨p.1.1, ((eq_slineOf_iff hc p.1 s).1 p.2.symm)⟩
        invFun := fun p => ⟨⟨p.1, s.2 _ p.2⟩, ((eq_slineOf_iff hc ⟨p.1, s.2 _ p.2⟩ s).2 p.2).symm⟩
        left_inv := fun p => rfl
        right_inv := fun p => rfl }
    rw [Fintype.card_congr e, ← Nat.card_eq_fintype_card]
    exact card_points_hline s.1
  have h1 : Fintype.card (PtPi c) = Fintype.card (SLine c) * (Fintype.card F + 1) := by
    rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv (slineOf hc)), Fintype.card_sigma]
    simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [card_pointsPi hc] at h1
  exact (Nat.eq_of_mul_eq_mul_right (Nat.succ_pos _) h1).symm

end BipartiteDD.HexagonD
