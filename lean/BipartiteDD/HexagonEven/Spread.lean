import BipartiteDD.HexagonEven.PiCount
import BipartiteDD.HexagonEven.Main
import BipartiteDD.HexagonD.Polygon

/-! Theorem D, slice 2, part 4 (target 1): `S` is a spread of `Π ∩ Q`.

For a finite field `F` of odd characteristic and `d ∈ F` with `-d` a non-square, `S = SLineE d` is the set of
`H(q)`-lines contained in `Π : x₀ + d x₄ = 0`.
* `existsUnique_slineE`: every singular point of `Π` lies on exactly one line of `S`;
* `sline_oppE`, `sline_edistE`: two distinct lines of `S` are opposite, i.e. at distance `6` in the
  incidence graph (`edist = 6`);
* `card_slineE`: `|S| = q³ + 1`. -/

namespace BipartiteDD.HexagonEven

open BipartiteDD.HexagonD

open BipartiteDD.Hexagon Module Submodule

variable {F : Type*} [Field F] [Fintype F] {d : F}

noncomputable instance fintypeHLine : Fintype (HLine F) :=
  haveI := finite_hline_even (F := F); Fintype.ofFinite _

noncomputable instance fintypeSLine (d : F) : Fintype (SLineE d) := Fintype.ofFinite _

theorem rep_not_mem_span_of_ne {p p' : Projectivization F (V7 F)} (h : p ≠ p') :
    p'.rep ∉ span F {p.rep} := by
  intro hmem
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
  apply h
  symm
  rw [← Projectivization.mk_rep p', ← Projectivization.mk_rep p, Projectivization.mk_eq_mk_iff']
  exact ⟨a, ha⟩

/-- The `S`-line through a singular point of `Π`. -/
noncomputable def slineOfE (hd : ∀ t : F, t ^ 2 + t + d ≠ 0) (hchar : (2 : F) = 0) (p : PtPiE d) : SLineE d :=
  (exists_slineE hd hchar p.1.1.rep_nonzero p.1.2 p.2).choose

theorem mem_slineOfE (hd : ∀ t : F, t ^ 2 + t + d ≠ 0) (hchar : (2 : F) = 0) (p : PtPiE d) : p.1.1.rep ∈ (slineOfE hd hchar p).1.1 :=
  (exists_slineE hd hchar p.1.1.rep_nonzero p.1.2 p.2).choose_spec

theorem eq_slineOfE_iff (hd : ∀ t : F, t ^ 2 + t + d ≠ 0) (hchar : (2 : F) = 0) (p : PtPiE d) (s : SLineE d) :
    s = slineOfE hd hchar p ↔ p.1.1.rep ∈ s.1.1 :=
  ⟨fun h => h ▸ mem_slineOfE hd hchar p, fun h =>
    slineE_unique hd hchar p.1.1.rep_nonzero p.1.2 p.2 h (mem_slineOfE hd hchar p)⟩

/-- Every singular point of `Π` lies on exactly one line of `S`. -/
theorem existsUnique_slineE (hd : ∀ t : F, t ^ 2 + t + d ≠ 0) (hchar : (2 : F) = 0) (p : SPt F) (hp : p.1.rep 0 + p.1.rep 3 + d * p.1.rep 4 = 0) :
    ∃! s : SLineE d, p.1.rep ∈ s.1.1 :=
  ⟨slineOfE hd hchar ⟨p, hp⟩, mem_slineOfE hd hchar ⟨p, hp⟩, fun s hs =>
    (eq_slineOfE_iff hd hchar ⟨p, hp⟩ s).2 hs⟩

/-- Distinct lines of `S` are far apart: no point of one is collinear with a point of the other. -/
theorem sline_oppE (hd : ∀ t : F, t ^ 2 + t + d ≠ 0) (hchar : (2 : F) = 0) {s s' : SLineE d} (hne : s ≠ s') :
    Opp (hexInc (F := F)) s.1 s'.1 := by
  rintro ⟨p, M, p', h1, h2, h3, h4⟩
  have h1' : p.1.rep ∈ s.1.1 := h1
  have h2' : p.1.rep ∈ M.1 := h2
  have h3' : p'.1.rep ∈ M.1 := h3
  have h4' : p'.1.rep ∈ s'.1.1 := h4
  have hpL : p.1.rep 0 + p.1.rep 3 + d * p.1.rep 4 = 0 := s.2 _ h1'
  have hp'L : p'.1.rep 0 + p'.1.rep 3 + d * p'.1.rep 4 = 0 := s'.2 _ h4'
  by_cases hpp : p = p'
  · subst hpp
    exact hne (slineE_unique hd hchar p.1.rep_nonzero p.2 hpL h1' h4')
  · have hMspan : M.1 = span F {p.1.rep, p'.1.rep} :=
      hline_eq_span M h2' h3' p.1.rep_nonzero (rep_not_mem_span_of_ne (fun h => hpp (Subtype.ext h)))
    have hM : InPiE d M := by
      intro x hx
      rw [hMspan] at hx
      obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hx
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination a * hpL + b * hp'L
    have e1 := slineE_unique hd hchar p.1.rep_nonzero p.2 hpL (s := ⟨M, hM⟩) (s' := s) h2' h1'
    have e2 := slineE_unique hd hchar p'.1.rep_nonzero p'.2 hp'L (s := ⟨M, hM⟩) (s' := s') h3' h4'
    exact hne (e1.symm.trans e2)

/-- Distinct lines of `S` are opposite: they are at distance `6` in the incidence graph of `H(q)`. -/
theorem sline_edistE (hd : ∀ t : F, t ^ 2 + t + d ≠ 0) (hchar : (2 : F) = 0) {s s' : SLineE d} (hne : s ≠ s') :
    (Hexagon.incGraph (hexInc (F := F))).edist (.inr s.1) (.inr s'.1) = 6 :=
  edist_eq_six_of_opp genPolygonGraph_hexagon_even (sline_oppE hd hchar hne)

/-- Number of points of an `S`-line: all of its points are singular points of `Π`. -/
theorem card_slineE [DecidableEq F] (hd : ∀ t : F, t ^ 2 + t + d ≠ 0) (hchar : (2 : F) = 0) :
    Fintype.card (SLineE d) = Fintype.card F ^ 3 + 1 := by
  classical
  have hfib : ∀ s : SLineE d, Fintype.card {p : PtPiE d // slineOfE hd hchar p = s} =
      Fintype.card F + 1 := by
    intro s
    have e : {p : PtPiE d // slineOfE hd hchar p = s} ≃ {p : SPt F // p.1.rep ∈ s.1.1} :=
      { toFun := fun p => ⟨p.1.1, ((eq_slineOfE_iff hd hchar p.1 s).1 p.2.symm)⟩
        invFun := fun p => ⟨⟨p.1, s.2 _ p.2⟩, ((eq_slineOfE_iff hd hchar ⟨p.1, s.2 _ p.2⟩ s).2 p.2).symm⟩
        left_inv := fun p => rfl
        right_inv := fun p => rfl }
    rw [Fintype.card_congr e, ← Nat.card_eq_fintype_card]
    exact card_points_hline s.1
  have h1 : Fintype.card (PtPiE d) = Fintype.card (SLineE d) * (Fintype.card F + 1) := by
    rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv (slineOfE hd hchar)), Fintype.card_sigma]
    simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [card_pointsPiE hd hchar] at h1
  exact (Nat.eq_of_mul_eq_mul_right (Nat.succ_pos _) h1).symm

end BipartiteDD.HexagonEven
