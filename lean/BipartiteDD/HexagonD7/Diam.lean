import BipartiteDD.HexagonD7.Cover

/-! Diameter 7 from a generalized hexagon, part 3: **Theorem 1** (THEOREM.md §3), `X` has diameter at most `7`.

Hypotheses (`Hyp`): every point is joined to every line by a walk of length at most `5` (F1); every point is
on two lines and every line has two points (F2); no two freed points are collinear (R1); `σ` maps the points
collinear with a freed point `r` onto the lines concurrent with `σ r` (R2); two hubs of the same type are
within `6`, either through the hexagon (owners within `4`) or through the hub graph (R3). -/

namespace BipartiteDD.HexagonD7

open SimpleGraph

variable {P L V U : Type*} {inc : P → L → Prop} {σ : P ≃ L} {R : Set P}
  {ownV : V → P} {ownU : U → P} {NS : V → U → Prop} {j : ℕ}

/-- The hypotheses of Theorem 1. -/
structure Hyp (inc : P → L → Prop) (σ : P ≃ L) (R : Set P) (ownV : V → P) (ownU : U → P)
    (NS : V → U → Prop) : Prop where
  pl : ∀ p l, Reach (Hexagon.incGraph inc) (.inl p) (.inr l) 5
  p2 : ∀ p, ∃ l l', l ≠ l' ∧ inc p l ∧ inc p l'
  l2 : ∀ l, ∃ p p', p ≠ p' ∧ inc p l ∧ inc p' l
  r1 : ∀ r ∈ R, ∀ s ∈ R, ¬ Coll inc r s
  r2 : ∀ r ∈ R, ∀ p, Coll inc r p ↔ Conc inc (σ r) (σ p)
  ownV_mem : ∀ v, ownV v ∈ R
  ownU_mem : ∀ u, ownU u ∈ R
  r3V : ∀ v v', Reach (Hexagon.incGraph inc) (.inl (ownV v)) (.inl (ownV v')) 4 ∨
    Reach (hubGraph NS) (.inl v) (.inl v') 6
  r3U : ∀ u u', Reach (Hexagon.incGraph inc) (.inr (σ (ownU u))) (.inr (σ (ownU u'))) 4 ∨
    Reach (hubGraph NS) (.inr u) (.inr u') 6

section Homs

variable (inc σ R ownV ownU NS j)

/-- Level `i` as a copy of the incidence graph. -/
def lvl (i : ZMod (2 * j + 1)) : Hexagon.incGraph inc →g X inc σ R ownV ownU NS j where
  toFun x := .inl (x, i)
  map_rel' := by
    intro a b h
    rcases a with p | l <;> rcases b with p' | l'
    · exact absurd h Hexagon.incGraph_not_adj_inl_inl
    · exact (SimpleGraph.fromRel_adj _ _ _).2 ⟨by simp, Or.inl (Or.inl ⟨h, rfl⟩)⟩
    · exact (SimpleGraph.fromRel_adj _ _ _).2 ⟨by simp, Or.inr (Or.inl ⟨h, rfl⟩)⟩
    · exact absurd h Hexagon.incGraph_not_adj_inr_inr

/-- The hub graph inside `X`. -/
def hubHom : hubGraph NS →g X inc σ R ownV ownU NS j where
  toFun x := .inr x
  map_rel' := by
    intro a b h
    rcases (SimpleGraph.fromRel_adj _ _ _).1 h with ⟨hne, h' | h'⟩
    · rcases a with v | u <;> rcases b with v' | u'
      · exact absurd h' id
      · exact (SimpleGraph.fromRel_adj _ _ _).2 ⟨by simp, Or.inl h'⟩
      · exact absurd h' id
      · exact absurd h' id
    · rcases a with v | u <;> rcases b with v' | u'
      · exact absurd h' id
      · exact absurd h' id
      · exact (SimpleGraph.fromRel_adj _ _ _).2 ⟨by simp, Or.inr h'⟩
      · exact absurd h' id

end Homs

theorem adj_shift {p : P} (hp : p ∉ R) {i i' : ZMod (2 * j + 1)} (h : Shift j i i') :
    (X inc σ R ownV ownU NS j).Adj (.inl (.inl p, i)) (.inl (.inr (σ p), i')) :=
  (SimpleGraph.fromRel_adj _ _ _).2 ⟨by simp, Or.inl (Or.inr ⟨hp, rfl, h⟩)⟩

theorem adj_hubV (v : V) (i : ZMod (2 * j + 1)) :
    (X inc σ R ownV ownU NS j).Adj (.inr (.inl v)) (.inl (.inl (ownV v), i)) :=
  (SimpleGraph.fromRel_adj _ _ _).2 ⟨by simp, Or.inl rfl⟩

theorem adj_hubU (u : U) (i : ZMod (2 * j + 1)) :
    (X inc σ R ownV ownU NS j).Adj (.inr (.inr u)) (.inl (.inr (σ (ownU u)), i)) :=
  (SimpleGraph.fromRel_adj _ _ _).2 ⟨by simp, Or.inl rfl⟩

/-- Two different levels differ by a shift `1 ≤ k ≤ j` one way or the other. -/
theorem shift_or {i i' : ZMod (2 * j + 1)} (h : i ≠ i') : Shift j i i' ∨ Shift j i' i := by
  set d := (i' - i).val with hd
  have hdlt : d < 2 * j + 1 := ZMod.val_lt _
  have hcast : ((d : ℕ) : ZMod (2 * j + 1)) = i' - i := ZMod.natCast_zmod_val _
  have hd0 : d ≠ 0 := by
    intro h0
    apply h
    have : i' - i = 0 := (ZMod.val_eq_zero (i' - i)).1 h0
    exact (sub_eq_zero.1 this).symm
  by_cases hdj : d ≤ j
  · left
    exact ⟨d, by omega, hdj, by rw [hcast]; ring⟩
  · right
    refine ⟨2 * j + 1 - d, by omega, by omega, ?_⟩
    have : ((2 * j + 1 - d : ℕ) : ZMod (2 * j + 1)) = -(i' - i) := by
      rw [Nat.cast_sub hdlt.le, ZMod.natCast_self, hcast]; ring
    rw [this]; ring

section Main

variable (H : Hyp inc σ R ownV ownU NS)
include H

theorem Hyp.pp6 (p p' : P) : Reach (Hexagon.incGraph inc) (.inl p) (.inl p') 6 := by
  obtain ⟨l, -, -, hl, -⟩ := H.p2 p'
  exact (H.pl p l).trans (Reach.adj (Hexagon.incGraph_adj_inr_inl.2 hl))

theorem Hyp.ll6 (l l' : L) : Reach (Hexagon.incGraph inc) (.inr l) (.inr l') 6 := by
  obtain ⟨a, -, -, ha, -⟩ := H.l2 l'
  exact (H.pl a l).symm.trans (Reach.adj (Hexagon.incGraph_adj_inl_inr.2 ha))

theorem Hyp.all6 (x y : P ⊕ L) : Reach (Hexagon.incGraph inc) x y 6 := by
  rcases x with p | l <;> rcases y with p' | l'
  · exact H.pp6 p p'
  · exact (H.pl p l').mono (by norm_num)
  · exact (H.pl p' l).symm.mono (by norm_num)
  · exact H.ll6 l l'

theorem Hyp.level (x y : P ⊕ L) (i : ZMod (2 * j + 1)) :
    Reach (X inc σ R ownV ownU NS j) (.inl (x, i)) (.inl (y, i)) 6 :=
  (H.all6 x y).map (lvl inc σ R ownV ownU NS j i)

/-- Case 4: a freed point reaches every point of a shifted level within `6`. -/
theorem Hyp.freed_point {a : P} (ha : a ∈ R) (b : P) {i i' : ZMod (2 * j + 1)} (hs : Shift j i i') :
    Reach (X inc σ R ownV ownU NS j) (.inl (.inl a, i)) (.inl (.inl b, i')) 6 := by
  obtain ⟨ℓ', hconc, hreach⟩ := cover H.p2 (H.pl b (σ a)).symm
  set p' := σ.symm ℓ' with hp'
  have hσ : σ p' = ℓ' := by simp [hp']
  have hconc' : Conc inc (σ a) (σ p') := by rw [hσ]; exact hconc
  have hcoll : Coll inc a p' := (H.r2 a ha p').2 hconc'
  have hp'R : p' ∉ R := fun hp => H.r1 a ha p' hp hcoll
  have h1 := hcoll.reach.map (lvl inc σ R ownV ownU NS j i)
  have h2 := Reach.adj (adj_shift (inc := inc) (σ := σ) (ownV := ownV) (ownU := ownU) (NS := NS) hp'R hs)
  have h3 := hreach.map (lvl inc σ R ownV ownU NS j i')
  rw [← hσ] at h3
  exact ((h1.trans h2).trans h3).mono (by norm_num)

/-- Cases 1–6: two vertices in levels `i` and `i + k`, `1 ≤ k ≤ j`. -/
theorem Hyp.cross (x y : P ⊕ L) {i i' : ZMod (2 * j + 1)} (hs : Shift j i i') :
    Reach (X inc σ R ownV ownU NS j) (.inl (x, i)) (.inl (y, i')) 7 := by
  rcases x with a | a
  · by_cases ha : a ∈ R
    · rcases y with b | b
      · exact (H.freed_point ha b hs).mono (by norm_num)
      · obtain ⟨c, -, -, hc, -⟩ := H.l2 b
        have h1 := H.freed_point ha c hs
        have h2 : (X inc σ R ownV ownU NS j).Adj (.inl (.inl c, i')) (.inl (.inr b, i')) :=
          (lvl inc σ R ownV ownU NS j i').map_rel (Hexagon.incGraph_adj_inl_inr.2 hc)
        exact h1.trans (Reach.adj h2)
    · have h1 := Reach.adj (adj_shift (inc := inc) (σ := σ) (ownV := ownV) (ownU := ownU) (NS := NS) ha hs)
      exact h1.trans (H.level (.inr (σ a)) y i')
  · rcases y with b | b
    · -- case 2
      obtain ⟨l, l', hne, hb, hb'⟩ := H.p2 b
      have hgood : ∃ w, inc b w ∧ σ.symm w ∉ R := by
        by_contra hcon
        push_neg at hcon
        have h1 := hcon l hb
        have h2 := hcon l' hb'
        have hconc : Conc inc (σ (σ.symm l)) (σ (σ.symm l')) := by
          simp only [Equiv.apply_symm_apply]; exact ⟨hne, b, hb, hb'⟩
        exact H.r1 _ h1 _ h2 ((H.r2 _ h1 _).2 hconc)
      obtain ⟨w, hbw, hw⟩ := hgood
      have h1 := (H.pl (σ.symm w) a).symm.map (lvl inc σ R ownV ownU NS j i)
      have h2 := Reach.adj (adj_shift (inc := inc) (σ := σ) (ownV := ownV) (ownU := ownU) (NS := NS) hw hs)
      rw [Equiv.apply_symm_apply] at h2
      have h3 : (X inc σ R ownV ownU NS j).Adj (.inl (.inr w, i')) (.inl (.inl b, i')) :=
        (lvl inc σ R ownV ownU NS j i').map_rel (Hexagon.incGraph_adj_inr_inl.2 hbw)
      exact (h1.trans h2).trans (Reach.adj h3)
    · by_cases hb : σ.symm b ∈ R
      · -- case 6
        set r := σ.symm b with hr
        obtain ⟨p', hcoll, hreach⟩ := cover_dual H.l2 (H.pl r a)
        have hp'R : p' ∉ R := fun hp => H.r1 r hb p' hp hcoll
        have hconc : Conc inc (σ r) (σ p') := (H.r2 r hb p').1 hcoll
        have h1 := hreach.symm.map (lvl inc σ R ownV ownU NS j i)
        have h2 := Reach.adj (adj_shift (inc := inc) (σ := σ) (ownV := ownV) (ownU := ownU) (NS := NS) hp'R hs)
        have h3 := hconc.reach.symm.map (lvl inc σ R ownV ownU NS j i')
        have hσr : σ r = b := by simp [hr]
        rw [hσr] at h3
        exact ((h1.trans h2).trans h3).mono (by norm_num)
      · -- case 3
        have h1 := (H.pl (σ.symm b) a).symm.map (lvl inc σ R ownV ownU NS j i)
        have h2 := Reach.adj (adj_shift (inc := inc) (σ := σ) (ownV := ownV) (ownU := ownU) (NS := NS) hb hs)
        rw [Equiv.apply_symm_apply] at h2
        exact (h1.trans h2).mono (by norm_num)

theorem Hyp.levels (x y : P ⊕ L) (i i' : ZMod (2 * j + 1)) :
    Reach (X inc σ R ownV ownU NS j) (.inl (x, i)) (.inl (y, i')) 7 := by
  by_cases h : i = i'
  · subst h; exact (H.level x y i).mono (by norm_num)
  · rcases shift_or h with hs | hs
    · exact H.cross x y hs
    · exact (H.cross y x hs).symm

theorem Hyp.hubV_level (v : V) (y : P ⊕ L) (i : ZMod (2 * j + 1)) :
    Reach (X inc σ R ownV ownU NS j) (.inr (.inl v)) (.inl (y, i)) 7 :=
  (Reach.adj (adj_hubV (inc := inc) (ownV := ownV) (σ := σ) (R := R) (ownU := ownU) (NS := NS) v i)).trans (H.level (.inl (ownV v)) y i)

theorem Hyp.hubU_level (u : U) (y : P ⊕ L) (i : ZMod (2 * j + 1)) :
    Reach (X inc σ R ownV ownU NS j) (.inr (.inr u)) (.inl (y, i)) 7 :=
  (Reach.adj (adj_hubU (inc := inc) (ownU := ownU) (σ := σ) (R := R) (ownV := ownV) (NS := NS) u i)).trans (H.level (.inr (σ (ownU u))) y i)

theorem Hyp.hubs (a b : V ⊕ U) : Reach (X inc σ R ownV ownU NS j) (.inr a) (.inr b) 7 := by
  rcases a with v | u <;> rcases b with v' | u'
  · rcases H.r3V v v' with h | h
    · have h1 := Reach.adj (adj_hubV (inc := inc) (ownV := ownV) (σ := σ) (R := R) (ownU := ownU) (NS := NS) (j := j) v 0)
      have h2 := h.map (lvl inc σ R ownV ownU NS j 0)
      have h3 := (Reach.adj (adj_hubV (inc := inc) (ownV := ownV) (σ := σ) (R := R) (ownU := ownU) (NS := NS) (j := j) v' 0)).symm
      exact ((h1.trans h2).trans h3).mono (by norm_num)
    · exact (h.map (hubHom inc σ R ownV ownU NS j)).mono (by norm_num)
  · have h1 := Reach.adj (adj_hubV (inc := inc) (ownV := ownV) (σ := σ) (R := R) (ownU := ownU) (NS := NS) (j := j) v 0)
    have h2 := (H.pl (ownV v) (σ (ownU u'))).map (lvl inc σ R ownV ownU NS j 0)
    have h3 := (Reach.adj (adj_hubU (inc := inc) (ownU := ownU) (σ := σ) (R := R) (ownV := ownV) (NS := NS) (j := j) u' 0)).symm
    exact (h1.trans h2).trans h3
  · have h1 := Reach.adj (adj_hubU (inc := inc) (ownU := ownU) (σ := σ) (R := R) (ownV := ownV) (NS := NS) (j := j) u 0)
    have h2 := (H.pl (ownV v') (σ (ownU u))).symm.map (lvl inc σ R ownV ownU NS j 0)
    have h3 := (Reach.adj (adj_hubV (inc := inc) (ownV := ownV) (σ := σ) (R := R) (ownU := ownU) (NS := NS) (j := j) v' 0)).symm
    exact (h1.trans h2).trans h3
  · rcases H.r3U u u' with h | h
    · have h1 := Reach.adj (adj_hubU (inc := inc) (ownU := ownU) (σ := σ) (R := R) (ownV := ownV) (NS := NS) (j := j) u 0)
      have h2 := h.map (lvl inc σ R ownV ownU NS j 0)
      have h3 := (Reach.adj (adj_hubU (inc := inc) (ownU := ownU) (σ := σ) (R := R) (ownV := ownV) (NS := NS) (j := j) u' 0)).symm
      exact ((h1.trans h2).trans h3).mono (by norm_num)
    · exact (h.map (hubHom inc σ R ownV ownU NS j)).mono (by norm_num)

/-- **Theorem 1 (distances).** Any two vertices of `X` are joined by a walk of length at most `7`. -/
theorem Hyp.reach7 (a b : Vtx P L V U j) : Reach (X inc σ R ownV ownU NS j) a b 7 := by
  rcases a with ⟨x, i⟩ | a <;> rcases b with ⟨y, i'⟩ | b
  · exact H.levels x y i i'
  · rcases b with v | u
    · exact (H.hubV_level v x i).symm
    · exact (H.hubU_level u x i).symm
  · rcases a with v | u
    · exact H.hubV_level v y i'
    · exact H.hubU_level u y i'
  · exact H.hubs a b

/-- **Theorem 1.** `X` has diameter at most `7`. -/
theorem Hyp.ediam_le : (X inc σ R ownV ownU NS j).ediam ≤ 7 :=
  SimpleGraph.ediam_le_iff.2 fun a b => (H.reach7 a b).edist_le

end Main

end BipartiteDD.HexagonD7
