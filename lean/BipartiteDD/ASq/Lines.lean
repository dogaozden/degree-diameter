import BipartiteDD.ASq.Defs
import BipartiteDD.GQST.Defs

/-! ASq, part 2: AS(q) is a generalized quadrangle of order `(q - 1, q + 1)`.

`ASq.isGQst` checks the four axioms of `GQst`. Lines have `q` points (`pts_on_line`), and a point lies
on the `q + 2` lines `dirLine p (dirOf o)` and `fibLine p.2` (`lines_on_pt`). Uniqueness of the line
through two points (`one_line`) and the quadrangle axiom (`gq_ax`) are direct coordinate checks. -/

namespace BipartiteDD.ASq

variable {F : Type*} [Field F]

/-- A line through two distinct points is either a fibre or a coset in the direction of their
difference, and its direction is then the difference. -/
theorem line_cases {l : Line F} {p r : F × F × F} (hpr : p ≠ r) (hp : p ∈ l) (hr : r ∈ l) :
    (l.carrier = fib p.2 ∧ r.2 = p.2) ∨ (l.carrier = lineA p (r.2 - p.2) ∧ r.2 ≠ p.2) := by
  rcases l.carrier_cases with ⟨g, d, hd, hl⟩ | ⟨w, hl⟩
  · have hp' : p ∈ lineA g d := by rw [← hl]; exact hp
    have hr' : r ∈ lineA g d := by rw [← hl]; exact hr
    have hpA : lineA p d = lineA g d := lineA_eq_of_mem hp'
    rw [← hpA] at hr'
    obtain ⟨s, hs⟩ := hr'
    have hs0 : s ≠ 0 := by
      rintro rfl
      apply hpr
      rw [← hs]
      simp
    have hsub : r.2 - p.2 = s • d := by
      rw [← hs]
      ext <;> simp only [Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
        ring
    have hr2 : r.2 ≠ p.2 := by
      intro h
      have h0 : s • d = 0 := by rw [← hsub, h, sub_self]
      exact (smul_eq_zero.mp h0).elim hs0 hd
    have hA : lineA p (r.2 - p.2) = lineA p d := by rw [hsub, lineA_smul p hs0]
    exact Or.inr ⟨by rw [hl, ← hpA, hA], hr2⟩
  · have hpw : p.2 = w := mem_fib_iff.mp (by rw [← hl]; exact hp)
    have hrw : r.2 = w := mem_fib_iff.mp (by rw [← hl]; exact hr)
    exact Or.inl ⟨by rw [hl, hpw], by rw [hrw, hpw]⟩

/-- Axiom `one_line`: two points on two lines force the lines to agree. -/
theorem one_line (p r : F × F × F) (l m : Line F) (hp : p ∈ l) (hr : r ∈ l) (hp' : p ∈ m)
    (hr' : r ∈ m) : p = r ∨ l = m := by
  by_cases hpr : p = r
  · exact Or.inl hpr
  · right
    rcases line_cases hpr hp hr with ⟨hl, hrw⟩ | ⟨hl, hrw⟩ <;>
      rcases line_cases hpr hp' hr' with ⟨hm, hrw'⟩ | ⟨hm, hrw'⟩
    · exact Line.ext (hl.trans hm.symm)
    · exact absurd hrw hrw'
    · exact absurd hrw' hrw
    · exact Line.ext (hl.trans hm.symm)

/-! ### Lines through a point -/

/-- Representatives of the `q + 1` directions: `(0, 1)` and `(1, t)`. -/
def dirOf : Option F → F × F
  | none => (0, 1)
  | some t => (1, t)

theorem dirOf_ne_zero (o : Option F) : dirOf o ≠ 0 := by
  cases o with
  | none =>
    intro h
    have := congrArg Prod.snd h
    simp [dirOf] at this
  | some t =>
    intro h
    have := congrArg Prod.fst h
    simp [dirOf] at this

/-- The lines through `p`, indexed by `Option (Option F)`: the fibre, then the `q + 1` cosets. -/
def thr (p : F × F × F) : Option (Option F) → Line F
  | none => fibLine p.2
  | some o => dirLine p (dirOf_ne_zero o)

theorem thr_mem (p : F × F × F) (i : Option (Option F)) : p ∈ thr p i := by
  cases i with
  | none => exact mem_fib_iff.mpr rfl
  | some o => exact mem_lineA_self p (dirOf o)

theorem dirOf_smul_eq {o o' : Option F} {s : F} (h : dirOf o = s • dirOf o') : o = o' := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  rcases o with _ | t <;> rcases o' with _ | u
  · rfl
  · dsimp only [dirOf, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2
    have hs : s = 0 := by linear_combination -h1
    subst hs
    simp at h2
  · dsimp only [dirOf, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2
    simp at h1
  · dsimp only [dirOf, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2
    have hs : s = 1 := by linear_combination -h1
    rw [hs, one_mul] at h2
    rw [h2]

/-- The witness point `p + (0, v)` of the coset `lineA p v`. -/
theorem pt_mem_lineA_one (p : F × F × F) (v : F × F) :
    (p.1 + det p.2 v, (p.2.1 + v.1, p.2.2 + v.2)) ∈ lineA p v :=
  ⟨1, by simp⟩

theorem lineA_ne_fib {p : F × F × F} {v : F × F} (hv : v ≠ 0) : lineA p v ≠ fib p.2 := by
  intro h
  have hy := pt_mem_lineA_one p v
  rw [h, mem_fib_iff] at hy
  apply hv
  have h1 : v.1 = 0 := by
    have := congrArg (fun x : F × F => x.1) hy
    simp only at this
    linear_combination this
  have h2 : v.2 = 0 := by
    have := congrArg (fun x : F × F => x.2) hy
    simp only at this
    linear_combination this
  exact Prod.ext h1 h2

theorem thr_injective (p : F × F × F) : Function.Injective (thr p) := by
  intro i j h
  have hc : (thr p i).carrier = (thr p j).carrier := congrArg Line.carrier h
  rcases i with _ | o <;> rcases j with _ | o'
  · rfl
  · exact absurd hc.symm (lineA_ne_fib (dirOf_ne_zero o'))
  · exact absurd hc (lineA_ne_fib (dirOf_ne_zero o))
  · have hc' : lineA p (dirOf o) = lineA p (dirOf o') := hc
    have hy : (p.1 + det p.2 (dirOf o), (p.2.1 + (dirOf o).1, p.2.2 + (dirOf o).2)) ∈
        lineA p (dirOf o') := by
      rw [← hc']
      exact pt_mem_lineA_one p (dirOf o)
    obtain ⟨s, hs⟩ := hy
    have hv : dirOf o = s • dirOf o' := by
      have h1 := congrArg (fun x : F × F × F => x.2.1) hs
      have h2 := congrArg (fun x : F × F × F => x.2.2) hs
      simp only at h1 h2
      refine Prod.ext ?_ ?_
      · simp only [Prod.smul_fst, smul_eq_mul]
        linear_combination -h1
      · simp only [Prod.smul_snd, smul_eq_mul]
        linear_combination -h2
    rw [dirOf_smul_eq hv]

theorem thr_surjective (p : F × F × F) (ℓ : Line F) (hp : p ∈ ℓ) : ∃ i, thr p i = ℓ := by
  rcases ℓ.carrier_cases with ⟨g, d, hd, hl⟩ | ⟨w, hl⟩
  · have hp' : p ∈ lineA g d := by rw [← hl]; exact hp
    have hpA : lineA p d = lineA g d := lineA_eq_of_mem hp'
    rcases eq_or_ne d.1 0 with h1 | h1
    · have h2 : d.2 ≠ 0 := fun h2 => hd (Prod.ext h1 h2)
      have hv : dirOf none = d.2⁻¹ • d :=
        Prod.ext (by simp [dirOf, h1]) (by simp [dirOf, h2])
      refine ⟨some none, Line.ext ?_⟩
      show lineA p (dirOf none) = ℓ.carrier
      rw [hv, lineA_smul p (inv_ne_zero h2), hl]
      exact hpA
    · have hv : dirOf (some (d.2 / d.1)) = d.1⁻¹ • d :=
        Prod.ext (by simp [dirOf, h1]) (by simp [dirOf, div_eq_inv_mul])
      refine ⟨some (some (d.2 / d.1)), Line.ext ?_⟩
      show lineA p (dirOf (some (d.2 / d.1))) = ℓ.carrier
      rw [hv, lineA_smul p (inv_ne_zero h1), hl]
      exact hpA
  · have hpw : p.2 = w := mem_fib_iff.mp (by rw [← hl]; exact hp)
    refine ⟨none, Line.ext ?_⟩
    show fib p.2 = ℓ.carrier
    rw [hl, hpw]

/-- The lines through `p` are in bijection with `Option (Option F)`. -/
theorem card_lines_through (p : F × F × F) [Fintype F] :
    Nat.card {ℓ : Line F // p ∈ ℓ} = Fintype.card F + 2 := by
  have hbij : Function.Bijective (fun i : Option (Option F) => (⟨thr p i, thr_mem p i⟩ :
      {ℓ : Line F // p ∈ ℓ})) := by
    constructor
    · intro i j h
      exact thr_injective p (congrArg Subtype.val h)
    · rintro ⟨ℓ, hℓ⟩
      obtain ⟨i, hi⟩ := thr_surjective p ℓ hℓ
      exact ⟨i, Subtype.ext hi⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card, Fintype.card_option,
    Fintype.card_option]

/-- Every line has `q` points. -/
theorem card_pts_on_line [Fintype F] (ℓ : Line F) : Nat.card {p // p ∈ ℓ} = Fintype.card F := by
  have key : ∃ f : F → F × F × F, Function.Injective f ∧ ℓ.carrier = Set.range f := by
    rcases ℓ.carrier_cases with ⟨g, d, hd, hl⟩ | ⟨w, hl⟩
    · refine ⟨fun t => (g.1 + t * det g.2 d, (g.2.1 + t * d.1, g.2.2 + t * d.2)), ?_, hl⟩
      intro t t' h
      have h2 := congrArg (fun x : F × F × F => x.2) h
      have h3 := congrArg (fun x : F × F => x.1) h2
      have h4 := congrArg (fun x : F × F => x.2) h2
      simp only at h3 h4
      rcases eq_or_ne d.1 0 with h1 | h1
      · have h5 : d.2 ≠ 0 := fun h5 => hd (Prod.ext h1 h5)
        have h6 : t * d.2 = t' * d.2 := by linear_combination h4
        exact mul_right_cancel₀ h5 h6
      · have h6 : t * d.1 = t' * d.1 := by linear_combination h3
        exact mul_right_cancel₀ h1 h6
    · exact ⟨fun μ => (μ, w), fun a b h => by simpa using congrArg Prod.fst h, hl⟩
  obtain ⟨f, hf, hr⟩ := key
  have hset : {p // p ∈ ℓ} = ↥(Set.range f) := by
    rw [← hr]
    rfl
  rw [hset, Nat.card_range_of_injective hf, Nat.card_eq_fintype_card]

/-- Axiom `gq_ax`: a point off a line is collinear with some point of the line. -/
theorem gq_ax [Fintype F] (p : F × F × F) (ℓ : Line F) (hp : p ∉ ℓ) :
    ∃ x : F × F × F, x ∈ ℓ ∧ ∃ m : Line F, p ∈ m ∧ x ∈ m := by
  rcases ℓ.carrier_cases with ⟨g, d, hd, hl⟩ | ⟨w, hl⟩
  · by_cases ht : ∃ t : F, p.2 = (g.2.1 + t * d.1, g.2.2 + t * d.2)
    · obtain ⟨t, ht⟩ := ht
      have hx : (g.1 + t * det g.2 d, (g.2.1 + t * d.1, g.2.2 + t * d.2)) ∈ ℓ := by
        rw [mem_line_iff, hl]
        exact ⟨t, rfl⟩
      refine ⟨_, hx, fibLine p.2, mem_fib_iff.mpr rfl, mem_fib_iff.mpr ?_⟩
      exact ht.symm
    · have hK : det (p.2 - g.2) d ≠ 0 := by
        intro h0
        apply ht
        obtain ⟨t, ht'⟩ := exists_smul_of_det_eq_zero hd h0
        refine ⟨t, ?_⟩
        have h1 := congrArg Prod.fst ht'
        have h2 := congrArg Prod.snd ht'
        simp only [Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2
        exact Prod.ext (by dsimp only; linear_combination h1) (by dsimp only; linear_combination h2)
      obtain ⟨lam, hlam⟩ : ∃ lam : F, lam * det (p.2 - g.2) d = g.1 - p.1 - det p.2 g.2 :=
        ⟨(g.1 - p.1 - det p.2 g.2) / det (p.2 - g.2) d, div_mul_cancel₀ _ hK⟩
      have he0 : (g.2 - p.2) + lam • d ≠ 0 := by
        intro h0
        apply ht
        refine ⟨lam, ?_⟩
        have h1 := congrArg Prod.fst h0
        have h2 := congrArg Prod.snd h0
        simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
          Prod.smul_snd, smul_eq_mul, Prod.fst_zero, Prod.snd_zero] at h1 h2
        exact Prod.ext (by dsimp only; linear_combination -h1) (by dsimp only; linear_combination -h2)
      have hx : (g.1 + lam * det g.2 d, (g.2.1 + lam * d.1, g.2.2 + lam * d.2)) ∈ ℓ := by
        rw [mem_line_iff, hl]
        exact ⟨lam, rfl⟩
      refine ⟨_, hx, dirLine p he0, ?_, ?_⟩
      · exact mem_lineA_self p _
      · show _ ∈ lineA p _
        refine ⟨1, Prod.ext ?_ (Prod.ext ?_ ?_)⟩
        · have hlam' := hlam
          simp only [det, Prod.fst_sub, Prod.snd_sub] at hlam'
          simp only [one_mul, det, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
            Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
          linear_combination hlam'
        · simp only [one_mul, Prod.fst_add, Prod.fst_sub, Prod.smul_fst, smul_eq_mul]
          ring
        · simp only [one_mul, Prod.snd_add, Prod.snd_sub, Prod.smul_snd, smul_eq_mul]
          ring
  · have hpw : p.2 ≠ w := fun h => hp (by rw [mem_line_iff, hl]; exact mem_fib_iff.mpr h)
    have hd : w - p.2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hpw)
    have hx : (p.1 + det p.2 (w - p.2), w) ∈ ℓ := by
      rw [mem_line_iff, hl]
      exact ⟨p.1 + det p.2 (w - p.2), rfl⟩
    refine ⟨_, hx, dirLine p hd, ?_, ?_⟩
    · exact mem_lineA_self p _
    · show _ ∈ lineA p _
      refine ⟨1, Prod.ext ?_ (Prod.ext ?_ ?_)⟩
      · simp only [one_mul, det, Prod.fst_sub, Prod.snd_sub]
      · simp only [one_mul, Prod.fst_sub]
        ring
      · simp only [one_mul, Prod.snd_sub]
        ring

/-- The number of lines is the number of points times `t + 1` over `s + 1`. -/
theorem card_mul_eq {P L : Type*} [Membership P L] [Fintype P] [Fintype L] {s t : ℕ}
    (G : BipartiteDD.GQst P L s t) : Fintype.card P * (t + 1) = Fintype.card L * (s + 1) := by
  classical
  have h := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (r := fun (p : P) (l : L) =>
    p ∈ l) (s := Finset.univ) (t := Finset.univ)
  have hA : ∀ p : P, (Finset.univ.bipartiteAbove (fun (p : P) (l : L) => p ∈ l) p).card = t + 1 := by
    intro p
    rw [← G.lines_on_pt p, Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  have hB : ∀ l : L, (Finset.univ.bipartiteBelow (fun (p : P) (l : L) => p ∈ l) l).card = s + 1 := by
    intro l
    rw [← G.pts_on_line l, Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  simp only [hA, hB, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  exact h

/-- Statement 1: AS(q) is a generalized quadrangle of order `(q - 1, q + 1)`, where `q` is the order of
`F`. The hypothesis `ringChar F ≠ 2` is not used: the four axioms hold in every characteristic. -/
theorem isGQst [Fintype F] (_hF : ringChar F ≠ 2) :
    GQst (F × F × F) (Line F) (Fintype.card F - 1) (Fintype.card F + 1) where
  pts_on_line l := by
    rw [card_pts_on_line]
    have := Fintype.card_pos (α := F)
    omega
  lines_on_pt p := by
    rw [card_lines_through p]
  one_line p r l m hp hr hp' hr' := one_line p r l m hp hr hp' hr'
  gq_ax p l hp := gq_ax p l hp

end BipartiteDD.ASq
