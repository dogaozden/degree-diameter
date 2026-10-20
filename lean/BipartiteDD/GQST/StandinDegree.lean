import BipartiteDD.GQST.Standin
import BipartiteDD.GQST.Defs
import BipartiteDD.GQ4.Blowup

/-! Group GQST, part 8: degrees in the stand-in graph. Each neighbourhood lies in the range of a map from an explicit
finite type:
- point-side vertex `standVtx p j` (original point or copy, with stand-in index `j`): the `t + 1` original lines
  through `p`, and the line copies served by `(p, j)`; total `t + 1 + b`;
- original line `l`: the `s + 1` original points on `l`, and one copy per (point `x` on `l`, copy index);
  total `s + 1 + a`;
- line copy `c`: its `s + 1` stand-ins, one per point of `c.1`.
Hence every vertex has degree at most `max (s + 1 + a) (t + 1 + b)`. -/

namespace BipartiteDD.GQST

open SimpleGraph
open scoped Classical

variable {P L : Type*} [Membership P L] {s t : ℕ}
variable {w : P → ℕ} {m : L → ℕ}
  {σ : (c : Σ l, Fin (m l)) → (p : P) → p ∈ c.1 → Fin (w p + 1)}

/-- Two stand-in vertices with the same underlying point and the same index agree; and conversely. -/
theorem eq_of_standVtx_eq {p q : P} {j : Fin (w p + 1)} {k : Fin (w q + 1)}
    (h : standVtx p j = standVtx q k) : p = q ∧ j.val = k.val := by
  have h1 := congrArg ptOf h
  rw [ptOf_standVtx, ptOf_standVtx] at h1
  have h2 := congrArg stIdx h
  rw [stIdx_standVtx, stIdx_standVtx] at h2
  exact ⟨h1, h2⟩

/-- The neighbours of a point-side vertex `standVtx p j`: at most `t + 1 + b` of them, when `(p, j)` serves at most
`b` line copies. -/
theorem ncard_nbr_stand [Fintype P] [Fintype L] {s t : ℕ} (G : GQst P L s t) (b : ℕ)
    (hσ : ∀ (p : P) (j : Fin (w p + 1)),
      (Finset.univ.filter (fun c : Σ l, Fin (m l) => ∃ hp : p ∈ c.1, σ c p hp = j)).card ≤ b)
    (p : P) (j : Fin (w p + 1)) :
    ((standin P L w m σ).neighborSet (.inl (standVtx p j))).ncard ≤ t + 1 + b := by
  refine (GQ4.ncard_le_of_subset_range _
    (fun d : {l : L // p ∈ l} ⊕ {c : Σ l, Fin (m l) // ∃ hp : p ∈ c.1, σ c p hp = j} =>
      (match d with
        | .inl l => .inr (.inl l.1)
        | .inr c => .inr (.inr c.1) :
        (P ⊕ Σ p, Fin (w p)) ⊕ (L ⊕ Σ l, Fin (m l)))) ?_).trans ?_
  · rintro y hy
    rcases standin_nbr_inl ((mem_neighborSet _ _ _).1 hy) with ⟨l, rfl, hl⟩ | ⟨c, rfl, p', hp', hq⟩
    · rw [ptOf_standVtx] at hl
      exact ⟨.inl ⟨l, hl⟩, rfl⟩
    · obtain ⟨rfl, hjk⟩ := eq_of_standVtx_eq hq
      exact ⟨.inr ⟨c, hp', Fin.ext hjk.symm⟩, rfl⟩
  · have hc : Fintype.card {l : L // p ∈ l} = t + 1 := by
      rw [← Nat.card_eq_fintype_card]
      exact G.lines_on_pt p
    rw [Fintype.card_sum, hc, Fintype.card_subtype]
    have := hσ p j
    omega

/-- The neighbours of an original line: `s + 1` original points and the copies of the points on it. -/
theorem standin_ncard_nbr_line [Fintype P] [Fintype L] {s t : ℕ} (G : GQst P L s t) (a : ℕ)
    (hw : ∀ l : L, ∑ p ∈ Finset.univ.filter (fun p => p ∈ l), w p ≤ a) (l : L) :
    ((standin P L w m σ).neighborSet (.inr (.inl l))).ncard ≤ s + 1 + a := by
  refine (GQ4.ncard_le_of_subset_range _
    (fun d : {p : P // p ∈ l} ⊕ (Σ x : {x : P // x ∈ l}, Fin (w x.1)) =>
      (match d with
        | .inl p => .inl (.inl p.1)
        | .inr z => .inl (.inr ⟨z.1.1, z.2⟩) :
        (P ⊕ Σ p, Fin (w p)) ⊕ (L ⊕ Σ l, Fin (m l)))) ?_).trans ?_
  · rintro y hy
    obtain ⟨q, rfl, hq⟩ := standin_nbr_line ((mem_neighborSet _ _ _).1 hy)
    rcases q with p | ⟨x, i⟩
    · exact ⟨.inl ⟨p, hq⟩, rfl⟩
    · exact ⟨.inr ⟨⟨x, hq⟩, i⟩, rfl⟩
  · have hc : Fintype.card {p : P // p ∈ l} = s + 1 := by
      rw [← Nat.card_eq_fintype_card]
      exact G.pts_on_line l
    have hsum : ∑ x : {x : P // x ∈ l}, w x.1 = ∑ x ∈ Finset.univ.filter (fun x => x ∈ l), w x :=
      (Finset.sum_subtype (Finset.univ.filter (fun x => x ∈ l)) (by simp) w).symm
    simp only [Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin, hc, hsum]
    have := hw l
    omega

/-- The neighbours of a line copy: its `s + 1` stand-ins. -/
theorem standin_ncard_nbr_line_copy [Fintype P] [Fintype L] {s t : ℕ} (G : GQst P L s t)
    (c : Σ l, Fin (m l)) :
    ((standin P L w m σ).neighborSet (.inr (.inr c))).ncard ≤ s + 1 := by
  refine (GQ4.ncard_le_of_subset_range _
    (fun p : {p : P // p ∈ c.1} => (.inl (standVtx p.1 (σ c p.1 p.2)) :
      (P ⊕ Σ p, Fin (w p)) ⊕ (L ⊕ Σ l, Fin (m l)))) ?_).trans ?_
  · rintro y hy
    obtain ⟨p, hp, rfl⟩ := standin_nbr_line_copy ((mem_neighborSet _ _ _).1 hy)
    exact ⟨⟨p, hp⟩, rfl⟩
  · have hc : Fintype.card {p : P // p ∈ c.1} = s + 1 := by
      rw [← Nat.card_eq_fintype_card]
      exact G.pts_on_line c.1
    rw [hc]

/-- Group GQST, degrees: every vertex of the stand-in graph has degree at most `max (s + 1 + a) (t + 1 + b)`,
when every line has total point weight at most `a` and each stand-in serves at most `b` line copies. -/
theorem standin_degree [Fintype P] [Fintype L] {s t : ℕ} (G : GQst P L s t)
    (a b : ℕ)
    (hw : ∀ l : L, ∑ p ∈ Finset.univ.filter (fun p => p ∈ l), w p ≤ a)
    (hσ : ∀ (p : P) (j : Fin (w p + 1)),
      (Finset.univ.filter (fun c : Σ l, Fin (m l) => ∃ hp : p ∈ c.1, σ c p hp = j)).card ≤ b)
    (v : (P ⊕ Σ p, Fin (w p)) ⊕ (L ⊕ Σ l, Fin (m l))) :
    ((standin P L w m σ).neighborSet v).ncard ≤ max (s + 1 + a) (t + 1 + b) := by
  have h1 := le_max_left (s + 1 + a) (t + 1 + b)
  have h2 := le_max_right (s + 1 + a) (t + 1 + b)
  rcases v with q | l | c
  · obtain ⟨p, j, rfl⟩ := exists_standVtx q
    have := ncard_nbr_stand G b hσ p j
    omega
  · have := standin_ncard_nbr_line (σ := σ) (m := m) G a hw l
    omega
  · have := standin_ncard_nbr_line_copy (σ := σ) (w := w) G c
    omega

end BipartiteDD.GQST
