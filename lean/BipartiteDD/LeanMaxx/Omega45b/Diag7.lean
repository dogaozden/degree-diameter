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

lemma key7 : ∀ i j k l m n o : Fin 3,
    good7 (nzero ![![0, 1, 3] i, ![0, 1, 3] j, ![0, 1, 3] k, ![0, 1, 3] l, ![0, 1, 3] m,
        ![0, 1, 3] n, ![0, 1, 3] o])
      ((tab [![0, 1, 3] i, ![0, 1, 3] j, ![0, 1, 3] k, ![0, 1, 3] l, ![0, 1, 3] m,
        ![0, 1, 3] n, ![0, 1, 3] o]).getD 0 0) := by
  decide +kernel

end BipartiteDD.LeanMaxx.Omega45b
