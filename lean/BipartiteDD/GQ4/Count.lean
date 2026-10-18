import BipartiteDD.GQ4.Defs
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Tauto

/-! Bonus: a generalized quadrangle of order `(q, q)` has `(q + 1) (q ^ 2 + 1)` points.

The uniqueness half of the GQ axiom (for `p ∉ l`, at most one point of `l` is collinear with `p`) is
not recorded in `GQ`, so it is an extra hypothesis `uniq`. `Nonempty P` is needed: the empty
structure satisfies the other axioms and has no points.

Counting, with `p0` a fixed point:
- `T` = points collinear with `p0` (including `p0`), `B` = the rest; `|T| = q (q + 1) + 1`;
- `Lt` = lines through `p0` (`q + 1`), `Ln` = lines not through `p0`; `|P| = |L|`;
- each line in `Ln` has exactly one point in `T`, so `q` points in `B`, and each point of `B` is on
  `q + 1` lines of `Ln`: `|B| (q + 1) = |Ln| q`;
- `|P| = |T| + |B|` and `|Ln| + (q + 1) = |L|` give `|P| = (q + 1)(q² + 1)`. -/

namespace BipartiteDD

open scoped Classical
open Finset

namespace GQ

variable {P L : Type*} [Membership P L] {q : ℕ} [Fintype P] [Fintype L]

theorem card_lines_through (G : GQ P L q) (p : P) :
    (univ.filter (fun l : L => p ∈ l)).card = q + 1 := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact G.lines_on_pt p

theorem card_pts_on (G : GQ P L q) (l : L) :
    (univ.filter (fun p : P => p ∈ l)).card = q + 1 := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact G.pts_on_line l

/-- Each point lies on `q + 1` lines and each line has `q + 1` points, so there are as many points as
lines. -/
theorem card_pts_eq_card_lines (G : GQ P L q) : Fintype.card P = Fintype.card L := by
  have h := card_mul_eq_card_mul (s := (univ : Finset P)) (t := (univ : Finset L))
    (r := fun p l => p ∈ l) (m := q + 1) (n := q + 1)
    (fun p _ => G.card_lines_through p) (fun l _ => G.card_pts_on l)
  rw [Finset.card_univ, Finset.card_univ] at h
  exact Nat.eq_of_mul_eq_mul_right (Nat.succ_pos q) h

theorem card_points [Nonempty P] (G : GQ P L q)
    (uniq : ∀ (p : P) (l : L), p ∉ l → ∀ x y : P, x ∈ l → y ∈ l →
      (∃ m : L, p ∈ m ∧ x ∈ m) → (∃ m : L, p ∈ m ∧ y ∈ m) → x = y) :
    Fintype.card P = (q + 1) * (q ^ 2 + 1) := by
  obtain ⟨p0⟩ := ‹Nonempty P›
  set T := univ.filter (fun x : P => ∃ m : L, p0 ∈ m ∧ x ∈ m) with hT
  set B := univ.filter (fun x : P => ¬ ∃ m : L, p0 ∈ m ∧ x ∈ m) with hB
  set Lt := univ.filter (fun l : L => p0 ∈ l) with hLt
  set Ln := univ.filter (fun l : L => ¬ p0 ∈ l) with hLn
  -- partitions
  have hTB : T.card + B.card = Fintype.card P := by
    rw [← Finset.card_univ]
    exact Finset.card_filter_add_card_filter_not _
  have hLtLn : Lt.card + Ln.card = Fintype.card L := by
    rw [← Finset.card_univ]
    exact Finset.card_filter_add_card_filter_not _
  have hLtcard : Lt.card = q + 1 := G.card_lines_through p0
  -- the points collinear with `p0`
  have hp0T : p0 ∈ T := by
    obtain ⟨m, hm⟩ := G.exists_line p0
    exact mem_filter.2 ⟨mem_univ _, ⟨m, hm, hm⟩⟩
  have hTt : (T.erase p0).card * 1 = Lt.card * q := by
    refine card_mul_eq_card_mul (s := T.erase p0) (t := Lt) (r := fun x l => x ∈ l)
      (m := 1) (n := q) ?_ ?_
    · intro x hx
      obtain ⟨hne, hxT⟩ := mem_erase.1 hx
      obtain ⟨m, hpm, hxm⟩ := (mem_filter.1 hxT).2
      rw [Finset.card_eq_one]
      refine ⟨m, ?_⟩
      ext l
      simp only [Finset.bipartiteAbove, mem_filter, mem_singleton, hLt, mem_univ, true_and]
      constructor
      · rintro ⟨hl0, hxl⟩
        rcases G.one_line p0 x l m hl0 hxl hpm hxm with h | h
        · exact absurd h.symm hne
        · exact h
      · rintro rfl
        exact ⟨hpm, hxm⟩
    · intro l hl
      have hpl : p0 ∈ l := (mem_filter.1 hl).2
      have hset : (T.erase p0).filter (fun x => x ∈ l) =
          (univ.filter (fun x : P => x ∈ l)).erase p0 := by
        ext x
        simp only [mem_filter, mem_erase, mem_univ, true_and, hT]
        constructor
        · rintro ⟨⟨hne, ⟨m, _, _⟩⟩, hxl⟩
          exact ⟨hne, hxl⟩
        · rintro ⟨hne, hxl⟩
          exact ⟨⟨hne, ⟨l, hpl, hxl⟩⟩, hxl⟩
      show ((T.erase p0).filter (fun x => x ∈ l)).card = q
      rw [hset, Finset.card_erase_of_mem (mem_filter.2 ⟨mem_univ _, hpl⟩), G.card_pts_on l]
      omega
  have hTerase : (T.erase p0).card + 1 = T.card := Finset.card_erase_add_one hp0T
  have hTcard : T.card = q * (q + 1) + 1 := by
    rw [hLtcard] at hTt
    nlinarith
  -- lines avoiding `p0` against points not collinear with `p0`
  have hBLn : B.card * (q + 1) = Ln.card * q := by
    refine card_mul_eq_card_mul (s := B) (t := Ln) (r := fun x l => x ∈ l) (m := q + 1)
      (n := q) ?_ ?_
    · intro x hx
      have hxB : ¬ ∃ m : L, p0 ∈ m ∧ x ∈ m := (mem_filter.1 hx).2
      show (Ln.filter (fun l => x ∈ l)).card = q + 1
      rw [← G.card_lines_through x]
      congr 1
      ext l
      simp only [mem_filter, mem_univ, true_and, hLn]
      constructor
      · rintro ⟨_, hxl⟩
        exact hxl
      · intro hxl
        exact ⟨fun hpl => hxB ⟨l, hpl, hxl⟩, hxl⟩
    · intro l hl
      have hpl : ¬ p0 ∈ l := (mem_filter.1 hl).2
      obtain ⟨x0, hx0l, m0, hpm0, hx0m0⟩ := G.gq_ax p0 l hpl
      have hS1 : ((univ.filter (fun x : P => x ∈ l)).filter
          (fun x => ∃ m : L, p0 ∈ m ∧ x ∈ m)).card = 1 := by
        rw [Finset.card_eq_one]
        refine ⟨x0, Finset.eq_singleton_iff_unique_mem.2 ⟨?_, ?_⟩⟩
        · simp only [mem_filter, mem_univ, true_and]
          exact ⟨hx0l, ⟨m0, hpm0, hx0m0⟩⟩
        · intro y hy
          simp only [mem_filter, mem_univ, true_and] at hy
          obtain ⟨hyl, m1, hpm1, hym1⟩ := hy
          exact uniq p0 l hpl y x0 hyl hx0l ⟨m1, hpm1, hym1⟩ ⟨m0, hpm0, hx0m0⟩
      have hS2 := Finset.card_filter_add_card_filter_not (s := univ.filter (fun x : P => x ∈ l))
        (fun x => ∃ m : L, p0 ∈ m ∧ x ∈ m)
      rw [G.card_pts_on l, hS1] at hS2
      have hset2 : B.filter (fun x => x ∈ l) =
          (univ.filter (fun x : P => x ∈ l)).filter (fun x => ¬ ∃ m : L, p0 ∈ m ∧ x ∈ m) := by
        ext x
        simp only [mem_filter, mem_univ, true_and, hB]
        tauto
      show (B.filter (fun x => x ∈ l)).card = q
      rw [hset2]
      omega
  -- the counting identity, over `ℤ`
  have hPL : Fintype.card P = Fintype.card L := G.card_pts_eq_card_lines
  have key : ((Fintype.card P : ℕ) : ℤ) = ((q : ℤ) + 1) * ((q : ℤ) ^ 2 + 1) := by
    have h1 : ((T.card : ℕ) : ℤ) + ((B.card : ℕ) : ℤ) = ((Fintype.card P : ℕ) : ℤ) := by
      exact_mod_cast hTB
    have h3 : ((Ln.card : ℕ) : ℤ) + ((q : ℤ) + 1) = ((Fintype.card P : ℕ) : ℤ) := by
      have : Lt.card + Ln.card = Fintype.card P := by rw [hLtLn, hPL]
      rw [hLtcard] at this
      exact_mod_cast (by linarith : Ln.card + (q + 1) = Fintype.card P)
    have h2 : ((B.card : ℕ) : ℤ) * ((q : ℤ) + 1) = ((Ln.card : ℕ) : ℤ) * (q : ℤ) := by
      exact_mod_cast hBLn
    have ht : ((T.card : ℕ) : ℤ) = (q : ℤ) * ((q : ℤ) + 1) + 1 := by
      exact_mod_cast hTcard
    linear_combination h2 + (q : ℤ) * h3 - ((q : ℤ) + 1) * h1 + ((q : ℤ) + 1) * ht
  exact_mod_cast key

end GQ

end BipartiteDD
