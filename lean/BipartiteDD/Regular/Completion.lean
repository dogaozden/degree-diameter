import BipartiteDD.Regular.Defs
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Regularity, part 1b: the completion lemma.

Let `r : α → β → Prop` be the incidence relation of a bipartite graph in which every vertex has at most
`Δ` neighbours. The *deficit* of a vertex is `Δ` minus its degree. If the total deficit of the `α` side
equals that of the `β` side, every deficit is at most `s`, and the total deficit `T` is larger than
`2 s (Δ + s + 1)`, then new pairs can be added to `r` (never a pair already related) so that every vertex
has degree exactly `Δ`. Adding pairs adds edges between the two sides, so bipartiteness is kept and the
diameter bound cannot get worse.

Proof (REPORT.md, Theorem R, step 4).
* Stub matching (`exists_multiplicity`). Give each vertex as many stubs as its deficit. Hall's theorem
  matches every `α`-stub to a compatible `β`-stub (one whose vertex is not already related), because an
  `α`-stub is incompatible with at most `Δ s` of the `T` stubs on the other side and symmetrically.
  The matching is a multigraph `m a b` (the number of stubs of `a` matched to stubs of `b`).
* Smoothing (`exists_smooth`). If some pair has multiplicity at least two, a switch
  `m a b, m a' b' → m a b', m a' b` removes one repetition. A suitable matched pair `(a', b')` exists
  because the bad ones (`a' = a`, `b' = b`, `a b'` or `a' b` already related or already in the multigraph)
  carry total multiplicity at most `2 s (Δ + s + 1) < T`. -/

namespace BipartiteDD.Regular

open Finset
open scoped Classical

section Core

variable {α β : Type*} [Fintype α] [Fintype β]

/-- `m` is a multigraph supported on the allowed pairs `F` with degree `d a` at `a` and `e b` at `b`. -/
def IsMultiplicity (F : α → β → Prop) (d : α → ℕ) (e : β → ℕ) (m : α → β → ℕ) : Prop :=
  (∀ a b, m a b ≠ 0 → F a b) ∧ (∀ a, ∑ b, m a b = d a) ∧ (∀ b, ∑ a, m a b = e b)

theorem card_filter_fst {γ : Type*} [Fintype γ] (n : γ → ℕ) (g : γ) :
    (univ.filter fun x : (Σ c, Fin (n c)) => x.1 = g).card = n g := by
  have : (univ.filter fun x : (Σ c, Fin (n c)) => x.1 = g) =
      ({g} : Finset γ).sigma (fun c => (univ : Finset (Fin (n c)))) := by
    ext ⟨c', k⟩
    simp
  rw [this, card_sigma]
  simp

/-- The stubs whose vertex lies in `X` number `∑_{c ∈ X} n c`. -/
theorem card_filter_fst_mem {γ : Type*} [Fintype γ] (n : γ → ℕ) (X : Finset γ) :
    (univ.filter fun x : (Σ c, Fin (n c)) => x.1 ∈ X).card = ∑ c ∈ X, n c := by
  have : (univ.filter fun x : (Σ c, Fin (n c)) => x.1 ∈ X) =
      X.sigma (fun c => (univ : Finset (Fin (n c)))) := by
    ext ⟨c', k⟩
    simp
  rw [this, card_sigma]
  simp

/-- Stub matching: with total deficit `T ≥ 2 Δ s`, there is a multigraph on the allowed pairs with the
prescribed degrees. -/
theorem exists_multiplicity (F : α → β → Prop) (d : α → ℕ) (e : β → ℕ) (Δ s : ℕ)
    (hd : ∀ a, d a ≤ s) (he : ∀ b, e b ≤ s)
    (hFa : ∀ a, (univ.filter fun b => ¬ F a b).card ≤ Δ)
    (hFb : ∀ b, (univ.filter fun a => ¬ F a b).card ≤ Δ)
    (hsum : ∑ a, d a = ∑ b, e b) (hT : 2 * (Δ * s) ≤ ∑ a, d a) :
    ∃ m, IsMultiplicity F d e m := by
  classical
  have cardA : Fintype.card (Σ a, Fin (d a)) = ∑ a, d a := by simp [Fintype.card_sigma]
  have cardB : Fintype.card (Σ b, Fin (e b)) = ∑ b, e b := by simp [Fintype.card_sigma]
  -- stubs of `b` are incompatible with at most `Δ * s` stubs of the other side
  have hforbA : ∀ a, (univ.filter fun y : (Σ b, Fin (e b)) => ¬ F a y.1).card ≤ Δ * s := by
    intro a
    have h := card_filter_fst_mem e (univ.filter fun b => ¬ F a b)
    have hh : (univ.filter fun y : (Σ b, Fin (e b)) => ¬ F a y.1) =
        (univ.filter fun y : (Σ b, Fin (e b)) => y.1 ∈ univ.filter fun b => ¬ F a b) := by
      ext y
      simp
    rw [hh, h]
    calc ∑ b ∈ univ.filter (fun b => ¬ F a b), e b
        ≤ ∑ b ∈ univ.filter (fun b => ¬ F a b), s := sum_le_sum (fun b _ => he b)
      _ = (univ.filter fun b => ¬ F a b).card * s := by rw [sum_const, smul_eq_mul]
      _ ≤ Δ * s := Nat.mul_le_mul_right _ (hFa a)
  have hforbB : ∀ b, (univ.filter fun x : (Σ a, Fin (d a)) => ¬ F x.1 b).card ≤ Δ * s := by
    intro b
    have h := card_filter_fst_mem d (univ.filter fun a => ¬ F a b)
    have hh : (univ.filter fun x : (Σ a, Fin (d a)) => ¬ F x.1 b) =
        (univ.filter fun x : (Σ a, Fin (d a)) => x.1 ∈ univ.filter fun a => ¬ F a b) := by
      ext x
      simp
    rw [hh, h]
    calc ∑ a ∈ univ.filter (fun a => ¬ F a b), d a
        ≤ ∑ a ∈ univ.filter (fun a => ¬ F a b), s := sum_le_sum (fun a _ => hd a)
      _ = (univ.filter fun a => ¬ F a b).card * s := by rw [sum_const, smul_eq_mul]
      _ ≤ Δ * s := Nat.mul_le_mul_right _ (hFb b)
  -- Hall's condition
  let t : (Σ a, Fin (d a)) → Finset (Σ b, Fin (e b)) := fun x => univ.filter fun y => F x.1 y.1
  have hall : ∀ U : Finset (Σ a, Fin (d a)), U.card ≤ (U.biUnion t).card := by
    intro U
    by_cases hU : U.card ≤ Δ * s
    · rcases U.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
      · simp
      · have h1 : (t x).card + (univ.filter fun y : (Σ b, Fin (e b)) => ¬ F x.1 y.1).card =
            Fintype.card (Σ b, Fin (e b)) := by
          rw [← card_univ]
          exact card_filter_add_card_filter_not _
        have h2 := hforbA x.1
        have h3 : (t x).card ≤ (U.biUnion t).card :=
          card_le_card (subset_biUnion_of_mem t hx)
        omega
    · have hbig : U.biUnion t = univ := by
        refine eq_univ_of_forall fun y => ?_
        rw [mem_biUnion]
        by_contra hy
        push Not at hy
        apply hU
        refine (card_le_card (fun x hx => ?_)).trans (hforbB y.1)
        rw [mem_filter]
        exact ⟨mem_univ _, fun hF => hy x hx (by simp [t, hF])⟩
      rw [hbig, card_univ, cardB, ← hsum]
      exact (card_le_univ U).trans (by rw [cardA])
  obtain ⟨f, hf, hft⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hall
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hf, by rw [cardA, cardB, hsum]⟩
  refine ⟨fun a b => (univ.filter fun x : (Σ a, Fin (d a)) => x.1 = a ∧ (f x).1 = b).card,
    ?_, ?_, ?_⟩
  · intro a b hm
    obtain ⟨x, hx⟩ := card_pos.1 (Nat.pos_of_ne_zero hm)
    rw [mem_filter] at hx
    have := hft x
    simp only [t, mem_filter, mem_univ, true_and] at this
    rw [hx.2.1, hx.2.2] at this
    exact this
  · intro a
    have h := card_eq_sum_card_fiberwise (f := fun x : (Σ a, Fin (d a)) => (f x).1)
      (s := univ.filter fun x : (Σ a, Fin (d a)) => x.1 = a) (t := univ)
      (fun x _ => mem_coe.2 (mem_univ _))
    rw [card_filter_fst] at h
    rw [h]
    refine sum_congr rfl fun b _ => ?_
    rw [filter_filter]
  · intro b
    have h := card_eq_sum_card_fiberwise (f := fun x : (Σ a, Fin (d a)) => x.1)
      (s := univ.filter fun x : (Σ a, Fin (d a)) => (f x).1 = b) (t := univ)
      (fun x _ => mem_coe.2 (mem_univ _))
    have h2 : (univ.filter fun x : (Σ a, Fin (d a)) => (f x).1 = b).card =
        (univ.filter fun y : (Σ b, Fin (e b)) => y.1 = b).card := by
      refine card_bij (fun x _ => f x) (fun x hx => by simpa using hx) (fun x _ y _ h => hf h)
        (fun y hy => ?_)
      obtain ⟨x, rfl⟩ := hbij.2 y
      exact ⟨x, by simpa using hy, rfl⟩
    rw [card_filter_fst] at h2
    rw [← h2, h]
    refine sum_congr rfl fun a _ => ?_
    rw [filter_filter]
    exact congrArg card (filter_congr fun x _ => and_comm)

/-! ### Smoothing: from a multigraph to a simple graph -/

theorem sum_rowflag (m : α → β → ℕ) (d : α → ℕ) (hrow : ∀ a, ∑ b, m a b = d a) (p : α → Prop) [DecidablePred p] :
    ∑ a, ∑ b, (if p a then m a b else 0) = ∑ a, if p a then d a else 0 := by
  refine sum_congr rfl fun a _ => ?_
  by_cases h : p a
  · simp [h, hrow a]
  · simp [h]

theorem sum_colflag (m : α → β → ℕ) (e : β → ℕ) (hcol : ∀ b, ∑ a, m a b = e b) (q : β → Prop) [DecidablePred q] :
    ∑ a, ∑ b, (if q b then m a b else 0) = ∑ b, if q b then e b else 0 := by
  rw [sum_comm]
  refine sum_congr rfl fun b _ => ?_
  by_cases h : q b
  · simp [h, hcol b]
  · simp [h]

theorem sum_flag_le {γ : Type*} [Fintype γ] (p : γ → Prop) [DecidablePred p] (w : γ → ℕ) (s : ℕ) (hw : ∀ c, w c ≤ s) :
    ∑ c, (if p c then w c else 0) ≤ (univ.filter p).card * s := by
  calc ∑ c, (if p c then w c else 0) ≤ ∑ c, (if p c then s else 0) :=
        sum_le_sum fun c _ => by split_ifs <;> simp [hw c]
    _ = (univ.filter p).card * s := by rw [← sum_filter, sum_const, smul_eq_mul]

theorem card_pos_le_sum {γ : Type*} [Fintype γ] (w : γ → ℕ) :
    (univ.filter fun c => 0 < w c).card ≤ ∑ c, w c := by
  rw [card_filter]
  exact sum_le_sum fun c _ => by split_ifs with h <;> omega

/-- The switch: if the total multiplicity is larger than `2 s (Δ + s + 1)`, then for every pair `(a, b)`
there is a matched pair `(a', b')` that can be switched with it. -/
theorem exists_switch (F : α → β → Prop) (d : α → ℕ) (e : β → ℕ) (Δ s : ℕ)
    (hd : ∀ a, d a ≤ s) (he : ∀ b, e b ≤ s)
    (hFa : ∀ a, (univ.filter fun b => ¬ F a b).card ≤ Δ)
    (hFb : ∀ b, (univ.filter fun a => ¬ F a b).card ≤ Δ)
    (hbig : 2 * s * (Δ + s + 1) < ∑ a, d a)
    (m : α → β → ℕ) (hm : IsMultiplicity F d e m) (a : α) (b : β) :
    ∃ a' b', a' ≠ a ∧ b' ≠ b ∧ 0 < m a' b' ∧ F a b' ∧ F a' b ∧ m a b' = 0 ∧ m a' b = 0 := by
  obtain ⟨-, hrow, hcol⟩ := hm
  by_contra H
  push Not at H
  have hT : ∑ a, d a = ∑ a', ∑ b', m a' b' := by
    refine (sum_congr rfl fun a' _ => (hrow a').symm)
  have hpt : ∀ a' b', m a' b' ≤
      (if a' = a then m a' b' else 0) + (if b' = b then m a' b' else 0) +
      (if ¬ F a b' then m a' b' else 0) + (if ¬ F a' b then m a' b' else 0) +
      (if 0 < m a b' then m a' b' else 0) + (if 0 < m a' b then m a' b' else 0) := by
    intro a' b'
    by_cases h0 : m a' b' = 0
    · simp [h0]
    · have hpos : 0 < m a' b' := Nat.pos_of_ne_zero h0
      have hbad : a' = a ∨ b' = b ∨ ¬ F a b' ∨ ¬ F a' b ∨ 0 < m a b' ∨ 0 < m a' b := by
        by_contra hc
        push Not at hc
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hc
        exact H a' b' h1 h2 hpos h3 h4 (by omega) (by omega)
      rcases hbad with h | h | h | h | h | h <;> simp [h] <;> omega
  have hsum : ∑ a', ∑ b', m a' b' ≤
      ∑ a', ∑ b', ((if a' = a then m a' b' else 0) + (if b' = b then m a' b' else 0) +
      (if ¬ F a b' then m a' b' else 0) + (if ¬ F a' b then m a' b' else 0) +
      (if 0 < m a b' then m a' b' else 0) + (if 0 < m a' b then m a' b' else 0)) :=
    sum_le_sum fun a' _ => sum_le_sum fun b' _ => hpt a' b'
  simp only [sum_add_distrib] at hsum
  have s1 : ∑ a', ∑ b', (if a' = a then m a' b' else 0) = ∑ a', if a' = a then d a' else 0 :=
    sum_rowflag m d hrow (fun a' => a' = a)
  have s2 : ∑ a', ∑ b', (if b' = b then m a' b' else 0) = ∑ b', if b' = b then e b' else 0 :=
    sum_colflag m e hcol (fun b' => b' = b)
  have s3 : ∑ a', ∑ b', (if ¬ F a b' then m a' b' else 0) = ∑ b', if ¬ F a b' then e b' else 0 :=
    sum_colflag m e hcol (fun b' => ¬ F a b')
  have s4 : ∑ a', ∑ b', (if ¬ F a' b then m a' b' else 0) = ∑ a', if ¬ F a' b then d a' else 0 :=
    sum_rowflag m d hrow (fun a' => ¬ F a' b)
  have s5 : ∑ a', ∑ b', (if 0 < m a b' then m a' b' else 0) = ∑ b', if 0 < m a b' then e b' else 0 :=
    sum_colflag m e hcol (fun b' => 0 < m a b')
  have s6 : ∑ a', ∑ b', (if 0 < m a' b then m a' b' else 0) = ∑ a', if 0 < m a' b then d a' else 0 :=
    sum_rowflag m d hrow (fun a' => 0 < m a' b)
  rw [s1, s2, s3, s4, s5, s6] at hsum
  have b1 : ∑ a', (if a' = a then d a' else 0) = d a := by simp
  have b2 : ∑ b', (if b' = b then e b' else 0) = e b := by simp
  have b3 := sum_flag_le (fun b' => ¬ F a b') e s he
  have b4 := sum_flag_le (fun a' => ¬ F a' b) d s hd
  have b5 := sum_flag_le (fun b' => 0 < m a b') e s he
  have b6 := sum_flag_le (fun a' => 0 < m a' b) d s hd
  have c3 := Nat.mul_le_mul_right s (hFa a)
  have c4 := Nat.mul_le_mul_right s (hFb b)
  have c5 := card_pos_le_sum (fun b' => m a b')
  have c6 := card_pos_le_sum (fun a' => m a' b)
  rw [hrow a] at c5
  rw [hcol b] at c6
  have c5' := Nat.mul_le_mul_right s (c5.trans (hd a))
  have c6' := Nat.mul_le_mul_right s (c6.trans (he b))
  have := hd a
  have := he b
  rw [hT] at hbig
  nlinarith

/-- One switch applied to a multigraph. -/
theorem switch_multiplicity (F : α → β → Prop) (d : α → ℕ) (e : β → ℕ) (m : α → β → ℕ)
    (hm : IsMultiplicity F d e m) (a a' : α) (b b' : β) (haa : a' ≠ a) (hbb : b' ≠ b)
    (hab : 0 < m a b) (hab' : 0 < m a' b') (hF1 : F a b') (hF2 : F a' b) :
    ∃ m', IsMultiplicity F d e m' ∧
      (∀ x y, m' x y + (if x = a ∧ y = b then 1 else 0) + (if x = a' ∧ y = b' then 1 else 0) =
        m x y + (if x = a ∧ y = b' then 1 else 0) + (if x = a' ∧ y = b then 1 else 0)) := by
  obtain ⟨hsupp, hrow, hcol⟩ := hm
  refine ⟨fun x y => m x y + (if x = a ∧ y = b' then 1 else 0) + (if x = a' ∧ y = b then 1 else 0)
      - (if x = a ∧ y = b then 1 else 0) - (if x = a' ∧ y = b' then 1 else 0), ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x y hxy
    by_cases h1 : x = a ∧ y = b'
    · obtain ⟨rfl, rfl⟩ := h1
      exact hF1
    by_cases h2 : x = a' ∧ y = b
    · obtain ⟨rfl, rfl⟩ := h2
      exact hF2
    apply hsupp
    simp only [h1, h2, ite_false] at hxy
    split_ifs at hxy <;> omega
  · intro x
    beta_reduce
    have key : ∀ y, (m x y + (if x = a ∧ y = b' then 1 else 0) + (if x = a' ∧ y = b then 1 else 0)
        - (if x = a ∧ y = b then 1 else 0) - (if x = a' ∧ y = b' then 1 else 0)) +
        (if x = a ∧ y = b then 1 else 0) + (if x = a' ∧ y = b' then 1 else 0) =
        m x y + (if x = a ∧ y = b' then 1 else 0) + (if x = a' ∧ y = b then 1 else 0) := by
      intro y
      by_cases h1 : x = a ∧ y = b
      · obtain ⟨rfl, rfl⟩ := h1
        simp [haa.symm, hbb.symm]
        omega
      by_cases h2 : x = a' ∧ y = b'
      · obtain ⟨rfl, rfl⟩ := h2
        simp [haa, hbb]
        omega
      simp only [h1, h2, ite_false]
      split_ifs <;> omega
    have hs : ∑ y, ((m x y + (if x = a ∧ y = b' then 1 else 0) + (if x = a' ∧ y = b then 1 else 0)
        - (if x = a ∧ y = b then 1 else 0) - (if x = a' ∧ y = b' then 1 else 0)) +
        (if x = a ∧ y = b then 1 else 0) + (if x = a' ∧ y = b' then 1 else 0)) =
        ∑ y, (m x y + (if x = a ∧ y = b' then 1 else 0) + (if x = a' ∧ y = b then 1 else 0)) :=
      sum_congr rfl fun y _ => key y
    simp only [sum_add_distrib] at hs
    have e1 : ∑ y : β, (if x = a ∧ y = b then 1 else 0) = if x = a then 1 else 0 := by
      by_cases hx : x = a <;> simp [hx]
    have e2 : ∑ y : β, (if x = a' ∧ y = b' then 1 else 0) = if x = a' then 1 else 0 := by
      by_cases hx : x = a' <;> simp [hx]
    have e3 : ∑ y : β, (if x = a ∧ y = b' then 1 else 0) = if x = a then 1 else 0 := by
      by_cases hx : x = a <;> simp [hx]
    have e4 : ∑ y : β, (if x = a' ∧ y = b then 1 else 0) = if x = a' then 1 else 0 := by
      by_cases hx : x = a' <;> simp [hx]
    rw [e1, e2, e3, e4, hrow x] at hs
    omega
  · intro y
    beta_reduce
    have key : ∀ x, (m x y + (if x = a ∧ y = b' then 1 else 0) + (if x = a' ∧ y = b then 1 else 0)
        - (if x = a ∧ y = b then 1 else 0) - (if x = a' ∧ y = b' then 1 else 0)) +
        (if x = a ∧ y = b then 1 else 0) + (if x = a' ∧ y = b' then 1 else 0) =
        m x y + (if x = a ∧ y = b' then 1 else 0) + (if x = a' ∧ y = b then 1 else 0) := by
      intro x
      by_cases h1 : x = a ∧ y = b
      · obtain ⟨rfl, rfl⟩ := h1
        simp [haa.symm, hbb.symm]
        omega
      by_cases h2 : x = a' ∧ y = b'
      · obtain ⟨rfl, rfl⟩ := h2
        simp [haa, hbb]
        omega
      simp only [h1, h2, ite_false]
      split_ifs <;> omega
    have hs : ∑ x, ((m x y + (if x = a ∧ y = b' then 1 else 0) + (if x = a' ∧ y = b then 1 else 0)
        - (if x = a ∧ y = b then 1 else 0) - (if x = a' ∧ y = b' then 1 else 0)) +
        (if x = a ∧ y = b then 1 else 0) + (if x = a' ∧ y = b' then 1 else 0)) =
        ∑ x, (m x y + (if x = a ∧ y = b' then 1 else 0) + (if x = a' ∧ y = b then 1 else 0)) :=
      sum_congr rfl fun x _ => key x
    simp only [sum_add_distrib] at hs
    have e1 : ∑ x : α, (if x = a ∧ y = b then 1 else 0) = if y = b then 1 else 0 := by
      by_cases hy : y = b <;> simp [hy]
    have e2 : ∑ x : α, (if x = a' ∧ y = b' then 1 else 0) = if y = b' then 1 else 0 := by
      by_cases hy : y = b' <;> simp [hy]
    have e3 : ∑ x : α, (if x = a ∧ y = b' then 1 else 0) = if y = b' then 1 else 0 := by
      by_cases hy : y = b' <;> simp [hy]
    have e4 : ∑ x : α, (if x = a' ∧ y = b then 1 else 0) = if y = b then 1 else 0 := by
      by_cases hy : y = b <;> simp [hy]
    rw [e1, e2, e3, e4, hcol y] at hs
    omega
  · intro x y
    by_cases h1 : x = a ∧ y = b
    · obtain ⟨rfl, rfl⟩ := h1
      simp [haa.symm, hbb.symm]
      omega
    by_cases h2 : x = a' ∧ y = b'
    · obtain ⟨rfl, rfl⟩ := h2
      simp [haa, hbb]
      omega
    simp only [h1, h2, ite_false]
    split_ifs <;> omega

/-- The number of repetitions in a multigraph. -/
def excess (m : α → β → ℕ) : ℕ := ∑ x, ∑ y, (m x y - 1)

/-- A switch removes a repetition: the excess strictly drops. -/
theorem excess_switch_lt (m m' : α → β → ℕ) (a a' : α) (b b' : β) (haa : a' ≠ a) (hbb : b' ≠ b)
    (hab : 2 ≤ m a b) (h0 : m a b' = 0) (h0' : m a' b = 0)
    (heq : ∀ x y, m' x y + (if x = a ∧ y = b then 1 else 0) + (if x = a' ∧ y = b' then 1 else 0) =
        m x y + (if x = a ∧ y = b' then 1 else 0) + (if x = a' ∧ y = b then 1 else 0)) :
    excess m' < excess m := by
  have hpt : ∀ u v, m' u v - 1 ≤ m u v - 1 := by
    intro u v
    have h := heq u v
    by_cases c1 : u = a ∧ v = b
    · have c2 : ¬ (u = a' ∧ v = b') := fun c => haa (c.1.symm.trans c1.1)
      have c3 : ¬ (u = a ∧ v = b') := fun c => hbb (c.2.symm.trans c1.2)
      have c4 : ¬ (u = a' ∧ v = b) := fun c => haa (c.1.symm.trans c1.1)
      rw [if_pos c1, if_neg c2, if_neg c3, if_neg c4] at h
      omega
    by_cases c2 : u = a' ∧ v = b'
    · have c3 : ¬ (u = a ∧ v = b') := fun c => haa (c2.1.symm.trans c.1)
      have c4 : ¬ (u = a' ∧ v = b) := fun c => hbb (c2.2.symm.trans c.2)
      rw [if_neg c1, if_pos c2, if_neg c3, if_neg c4] at h
      omega
    by_cases c3 : u = a ∧ v = b'
    · have c4 : ¬ (u = a' ∧ v = b) := fun c => haa (c.1.symm.trans c3.1)
      have hm0 : m u v = 0 := by rw [c3.1, c3.2]; exact h0
      rw [if_neg c1, if_neg c2, if_pos c3, if_neg c4] at h
      omega
    by_cases c4 : u = a' ∧ v = b
    · have hm0 : m u v = 0 := by rw [c4.1, c4.2]; exact h0'
      rw [if_neg c1, if_neg c2, if_neg c3, if_pos c4] at h
      omega
    · rw [if_neg c1, if_neg c2, if_neg c3, if_neg c4] at h
      omega
  have hstrict : m' a b - 1 < m a b - 1 := by
    have h := heq a b
    have c2 : ¬ (a = a' ∧ b = b') := fun c => haa c.1.symm
    have c3 : ¬ (a = a ∧ b = b') := fun c => hbb c.2.symm
    have c4 : ¬ (a = a' ∧ b = b) := fun c => haa c.1.symm
    rw [if_pos ⟨rfl, rfl⟩, if_neg c2, if_neg c3, if_neg c4] at h
    omega
  unfold excess
  refine sum_lt_sum (fun x _ => sum_le_sum fun y _ => hpt x y) ⟨a, mem_univ _, ?_⟩
  exact sum_lt_sum (fun y _ => hpt a y) ⟨b, mem_univ _, hstrict⟩

/-- Smoothing: a multigraph with prescribed degrees can be made simple. -/
theorem exists_smooth (F : α → β → Prop) (d : α → ℕ) (e : β → ℕ) (Δ s : ℕ)
    (hd : ∀ a, d a ≤ s) (he : ∀ b, e b ≤ s)
    (hFa : ∀ a, (univ.filter fun b => ¬ F a b).card ≤ Δ)
    (hFb : ∀ b, (univ.filter fun a => ¬ F a b).card ≤ Δ)
    (hbig : 2 * s * (Δ + s + 1) < ∑ a, d a) :
    ∀ n, ∀ m, IsMultiplicity F d e m → excess m ≤ n →
      ∃ m', IsMultiplicity F d e m' ∧ ∀ x y, m' x y ≤ 1 := by
  intro n
  induction n with
  | zero =>
    intro m hm hex
    refine ⟨m, hm, fun x y => ?_⟩
    have h0 : ∑ x, ∑ y, (m x y - 1) = 0 := Nat.le_zero.1 hex
    rw [sum_eq_zero_iff] at h0
    have := (sum_eq_zero_iff.1 (h0 x (mem_univ _))) y (mem_univ _)
    omega
  | succ n ih =>
    intro m hm hex
    by_cases hall : ∀ x y, m x y ≤ 1
    · exact ⟨m, hm, hall⟩
    · push Not at hall
      obtain ⟨a, b, hab⟩ := hall
      obtain ⟨a', b', haa, hbb, hpos, hF1, hF2, h0, h0'⟩ :=
        exists_switch F d e Δ s hd he hFa hFb hbig m hm a b
      obtain ⟨m', hm', heq⟩ := switch_multiplicity F d e m hm a a' b b' haa hbb (by omega) hpos hF1 hF2
      have hlt := excess_switch_lt m m' a a' b b' haa hbb (by omega) h0 h0' heq
      exact ih m' hm' (by omega)

/-- **The core completion lemma.** Prescribed degrees `d` on `α` and `e` on `β`, each at most `s`, with
equal totals `T` larger than `2 s (Δ + s + 1)`, can be realised by a simple bipartite graph on the allowed
pairs `F`, provided each vertex has at most `Δ` forbidden partners. -/
theorem exists_degree_subgraph (F : α → β → Prop) (d : α → ℕ) (e : β → ℕ) (Δ s : ℕ)
    (hd : ∀ a, d a ≤ s) (he : ∀ b, e b ≤ s)
    (hFa : ∀ a, (univ.filter fun b => ¬ F a b).card ≤ Δ)
    (hFb : ∀ b, (univ.filter fun a => ¬ F a b).card ≤ Δ)
    (hsum : ∑ a, d a = ∑ b, e b) (hbig : 2 * s * (Δ + s + 1) < ∑ a, d a) :
    ∃ H : α → β → Prop, (∀ a b, H a b → F a b) ∧
      (∀ a, (univ.filter fun b => H a b).card = d a) ∧
      (∀ b, (univ.filter fun a => H a b).card = e b) := by
  have hT : 2 * (Δ * s) ≤ ∑ a, d a := by nlinarith
  obtain ⟨m, hm⟩ := exists_multiplicity F d e Δ s hd he hFa hFb hsum hT
  obtain ⟨m', ⟨hsupp, hrow, hcol⟩, hle⟩ := exists_smooth F d e Δ s hd he hFa hFb hbig _ m hm le_rfl
  refine ⟨fun a b => 0 < m' a b, fun a b h => hsupp a b (by omega), fun a => ?_, fun b => ?_⟩
  · rw [card_filter, ← hrow a]
    exact sum_congr rfl fun b _ => by have := hle a b; split_ifs <;> omega
  · rw [card_filter, ← hcol b]
    exact sum_congr rfl fun a _ => by have := hle a b; split_ifs <;> omega

end Core

/-! ### The completion lemma for bipartite graphs -/

section Graph

variable {α β : Type*}

/-- The degree of the left vertex `a` of the bipartite graph of `r`. -/
noncomputable def degL (r : α → β → Prop) (a : α) : ℕ := {b | r a b}.ncard

/-- The degree of the right vertex `b` of the bipartite graph of `r`. -/
noncomputable def degR (r : α → β → Prop) (b : β) : ℕ := {a | r a b}.ncard

theorem ncard_setOf_eq_card_filter {γ : Type*} [Fintype γ] (p : γ → Prop) :
    {c | p c}.ncard = (univ.filter p).card := by
  rw [← Set.ncard_coe_finset, Finset.coe_filter]
  simp

variable [Fintype α] [Fintype β]

theorem sum_degL_eq_sum_degR (r : α → β → Prop) : ∑ a, degL r a = ∑ b, degR r b := by
  unfold degL degR
  simp only [ncard_setOf_eq_card_filter, card_filter]
  exact sum_comm

/-- **The completion lemma.** Let `r` be a bipartite graph in which every vertex has degree at most `Δ`
and every deficit `Δ - deg` is at most `s`. If the two sides have the same number of vertices and the total
deficit `T` of the left side exceeds `2 s (Δ + s + 1)`, then some pairs can be added to `r`, none of them
already related, so that every vertex has degree exactly `Δ`. -/
theorem exists_regular_completion (r : α → β → Prop) (Δ s : ℕ)
    (hα : ∀ a, degL r a ≤ Δ) (hβ : ∀ b, degR r b ≤ Δ)
    (hsα : ∀ a, Δ - degL r a ≤ s) (hsβ : ∀ b, Δ - degR r b ≤ s)
    (hcard : Fintype.card α = Fintype.card β)
    (hbig : 2 * s * (Δ + s + 1) < ∑ a, (Δ - degL r a)) :
    ∃ r' : α → β → Prop, (∀ a b, r a b → r' a b) ∧ IsRegularOfDegree (biGraph r') Δ := by
  classical
  have hsum : ∑ a, (Δ - degL r a) = ∑ b, (Δ - degR r b) := by
    have h1 : ∑ a, (Δ - degL r a) + ∑ a, degL r a = Fintype.card α * Δ := by
      rw [← sum_add_distrib]
      rw [sum_congr rfl fun a _ => Nat.sub_add_cancel (hα a)]
      simp [mul_comm]
    have h2 : ∑ b, (Δ - degR r b) + ∑ b, degR r b = Fintype.card β * Δ := by
      rw [← sum_add_distrib]
      rw [sum_congr rfl fun b _ => Nat.sub_add_cancel (hβ b)]
      simp [mul_comm]
    have := sum_degL_eq_sum_degR r
    rw [hcard] at h1
    omega
  obtain ⟨H, hHF, hHa, hHb⟩ := exists_degree_subgraph (fun a b => ¬ r a b)
    (fun a => Δ - degL r a) (fun b => Δ - degR r b) Δ s hsα hsβ
    (fun a => by
      refine le_trans (card_le_card (t := univ.filter fun b => r a b)
        (fun b hb => by simpa using hb)) ?_
      rw [← ncard_setOf_eq_card_filter]
      exact hα a)
    (fun b => by
      refine le_trans (card_le_card (t := univ.filter fun a => r a b)
        (fun a ha => by simpa using ha)) ?_
      rw [← ncard_setOf_eq_card_filter]
      exact hβ b)
    hsum hbig
  refine ⟨fun a b => r a b ∨ H a b, fun a b h => Or.inl h, ?_⟩
  rw [biGraph_regular_iff]
  constructor
  · intro a
    have hset : {b | r a b ∨ H a b} = {b | r a b} ∪ {b | H a b} := Set.setOf_or
    rw [hset, Set.ncard_union_eq (s := {b | r a b}) (t := {b | H a b})
      (Set.disjoint_left.2 fun b hr hh => hHF a b hh hr) (Set.toFinite _) (Set.toFinite _), ncard_setOf_eq_card_filter (fun b => H a b), hHa a]
    have := hα a
    change degL r a + (Δ - degL r a) = Δ
    omega
  · intro b
    have hset : {a | r a b ∨ H a b} = {a | r a b} ∪ {a | H a b} := Set.setOf_or
    rw [hset, Set.ncard_union_eq (s := {a | r a b}) (t := {a | H a b})
      (Set.disjoint_left.2 fun a hr hh => hHF a b hh hr) (Set.toFinite _) (Set.toFinite _), ncard_setOf_eq_card_filter (fun a => H a b), hHb b]
    have := hβ b
    change degR r b + (Δ - degR r b) = Δ
    omega

/-- The completion lemma with the diameter bound: the completed graph is a `Δ`-regular bipartite graph of
diameter at most `D` whenever `r` has diameter at most `D`. -/
theorem exists_regular_completion_diam (r : α → β → Prop) (Δ s D : ℕ)
    (hα : ∀ a, degL r a ≤ Δ) (hβ : ∀ b, degR r b ≤ Δ)
    (hsα : ∀ a, Δ - degL r a ≤ s) (hsβ : ∀ b, Δ - degR r b ≤ s)
    (hcard : Fintype.card α = Fintype.card β)
    (hbig : 2 * s * (Δ + s + 1) < ∑ a, (Δ - degL r a)) (hD : (biGraph r).ediam ≤ D) :
    ∃ r' : α → β → Prop, (∀ a b, r a b → r' a b) ∧ IsBipartiteRegDiam (biGraph r') Δ D := by
  obtain ⟨r', hr', hreg⟩ := exists_regular_completion r Δ s hα hβ hsα hsβ hcard hbig
  exact ⟨r', hr', biGraph_colorable r', hreg, ediam_le_of_le (biGraph_mono hr') hD⟩

/-- The completion lemma on `Fin n`, where `n = 2 |α|` is the number of vertices. -/
theorem exists_regular_completion_fin (r : α → β → Prop) (Δ s D : ℕ)
    (hα : ∀ a, degL r a ≤ Δ) (hβ : ∀ b, degR r b ≤ Δ)
    (hsα : ∀ a, Δ - degL r a ≤ s) (hsβ : ∀ b, Δ - degR r b ≤ s)
    (hcard : Fintype.card α = Fintype.card β)
    (hbig : 2 * s * (Δ + s + 1) < ∑ a, (Δ - degL r a)) (hD : (biGraph r).ediam ≤ D) :
    ∃ G : SimpleGraph (Fin (2 * Fintype.card α)), IsBipartiteRegDiam G Δ D := by
  obtain ⟨r', -, h⟩ := exists_regular_completion_diam r Δ s D hα hβ hsα hsβ hcard hbig hD
  have hc : Fintype.card (α ⊕ β) = 2 * Fintype.card α := by
    rw [Fintype.card_sum, ← hcard]; ring
  exact ⟨(biGraph r').comap (Fintype.equivFinOfCardEq hc).symm,
    h.comap (Fintype.equivFinOfCardEq hc)⟩

end Graph

end BipartiteDD.Regular
