import BipartiteDD.LeanMaxx.Omega45b.Zcount

/-!
# Omega45b.Diag7: zero counts of diagonal quadratic forms in seven variables over `F7`

For a diagonal form `Σ wᵢ xᵢ²` on `F7^7` with `k = nzero w` zero weights (so of rank `7 - k`), the
number of zeros is exactly `7^6` when `k` is even (odd rank), and at most `7^6 + 6·7^((5+k)/2)`
when `k` is odd (even rank). This is the classical count `q^{n-1} + O((q-1) q^{n-1-r/2})`; here it
is checked by kernel computation over the `3^7` square-class patterns (`Zcount.tab`).
-/

namespace BipartiteDD.LeanMaxx.Omega45b

/-- The zero-count condition for seven variables with `k` zero weights. -/
def good7 (k Z : ℕ) : Prop := if k % 2 = 0 then Z = 7 ^ 6 else Z ≤ 7 ^ 6 + 6 * 7 ^ ((5 + k) / 2)

instance (k Z : ℕ) : Decidable (good7 k Z) := by unfold good7; infer_instance

lemma key7a (i j : Fin 3) : ∀ k l m n o : Fin 3,
    good7 (nzero ![![0, 1, 3] i, ![0, 1, 3] j, ![0, 1, 3] k, ![0, 1, 3] l, ![0, 1, 3] m,
        ![0, 1, 3] n, ![0, 1, 3] o])
      ((tab [![0, 1, 3] i, ![0, 1, 3] j, ![0, 1, 3] k, ![0, 1, 3] l, ![0, 1, 3] m,
        ![0, 1, 3] n, ![0, 1, 3] o]).getD 0 0) := by
  revert i j
  decide +kernel

lemma key7 : ∀ i j k l m n o : Fin 3,
    good7 (nzero ![![0, 1, 3] i, ![0, 1, 3] j, ![0, 1, 3] k, ![0, 1, 3] l, ![0, 1, 3] m,
        ![0, 1, 3] n, ![0, 1, 3] o])
      ((tab [![0, 1, 3] i, ![0, 1, 3] j, ![0, 1, 3] k, ![0, 1, 3] l, ![0, 1, 3] m,
        ![0, 1, 3] n, ![0, 1, 3] o]).getD 0 0) :=
  fun i j => key7a i j

theorem wzeros7 (w : Fin 7 → F7) : good7 (nzero w) (wzeros w) := by
  obtain ⟨i, hi⟩ := cls_mem (w 0)
  obtain ⟨j, hj⟩ := cls_mem (w 1)
  obtain ⟨k, hk⟩ := cls_mem (w 2)
  obtain ⟨l, hl⟩ := cls_mem (w 3)
  obtain ⟨m, hm⟩ := cls_mem (w 4)
  obtain ⟨n, hn⟩ := cls_mem (w 5)
  obtain ⟨o, ho⟩ := cls_mem (w 6)
  have hw : cls ∘ w = ![![0, 1, 3] i, ![0, 1, 3] j, ![0, 1, 3] k, ![0, 1, 3] l, ![0, 1, 3] m,
      ![0, 1, 3] n, ![0, 1, 3] o] := by
    ext x; fin_cases x <;> simp [hi, hj, hk, hl, hm, hn, ho]
  rw [← wzeros_cls, ← nzero_cls, hw, wzeros_eq]
  exact key7 i j k l m n o

end BipartiteDD.LeanMaxx.Omega45b
