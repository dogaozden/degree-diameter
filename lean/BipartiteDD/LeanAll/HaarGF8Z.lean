import BipartiteDD.LeanAll.HaarGF8

/-! # Haar graphs of `Z_n × SL(2,8)`

`HaarGF16.cover16` with the second factor over `GF8` (`HaarGF8.batchOK8`, `word_const8`): batch `i` fixes the matrix
of batch `i / 8` of `SL(2,8)` with free entry `i % 8`, and its slots are the `Z_n` values, checked by the `HaarSwar`
batch over `ZMod 2` with identity letters. -/

namespace BipartiteDD.LeanAll.HaarGF8Z

open BipartiteDD.LeanAll BipartiteDD.LeanAll.GF8 BipartiteDD.LeanAll.HaarSwar BipartiteDD.LeanAll.Swar
open BipartiteDD.LeanAll.HaarSL BipartiteDD.LeanAll.HaarPSL BipartiteDD.LeanAll.HaarProd BipartiteDD.LeanAll.HaarGF8
open Matrix

variable (s2 : ℕ → SpecialLinearGroup (Fin 2) GF8) (invAt : ℕ → Bool)

/-! ## The cover of `Z_n × SL(2,8)` -/

theorem flat8 {b j : ℕ} (hb : b < 8 * 8 - 1) (hj : j < 8) :
    (b * 8 + j) / 8 = b ∧ (b * 8 + j) % 8 = j ∧ b * 8 + j < (8 * 8 - 1) * 8 := by omega

/-- **The cover of `Z_n × SL(2,8)`.** Batch `i` fixes the matrix of batch `i / 8` of `SL(2,8)` with free entry
`i % 8`; slot `j` is the `Z_n` value `j`, checked by the `HaarSwar` batch check over `ZMod 2` whose letters `sZ` have
identity matrices. -/
theorem cover8 {n : ℕ} [NeZero n] (sZ : ℕ → G 2 n) (P : Prm) (hv : P.valid) (hw16 : 16 ≤ P.w) (hnP : P.n = n)
    (hN : P.N = n) {ONES RZ : ℕ} (hO : ONES = pkF P.w (fun _ => 1) P.N) (hRZ : RZ = pkF P.w (fun j => j % n) P.N)
    {lt : ℕ → ℕ → Let} {lm : ℕ → ℕ → Q8} (hlt : LetOK P lt) (hrep₁ : LetRep sZ invAt P.Δ P.L lt)
    (hrep₂ : LetRep8 s2 invAt P.Δ P.L lm)
    (hB : ∀ i < (8 * 8 - 1) * 8, ∃ Dig, batchOK P ONES lt Dig true ONES 0 0 0 RZ = true ∧
      batchOK8 P ONES lm Dig (kindB 8 (i / 8)) (sp (mk (aB 8 (i / 8))) * ONES) (sp (mk (i % 8)) * ONES)
        (sp (mk (cB 8 (i / 8))) * ONES) (sp (mk (i % 8)) * ONES) = true) :
    ∀ x : Multiplicative (ZMod n) × SpecialLinearGroup (Fin 2) GF8, ∃ dg : ℕ → ℕ, (∀ t < P.L, dg t < P.Δ) ∧
      wordX (fun u => ((sZ u).2, s2 u)) invAt dg P.L = x := by
  intro ⟨z, A⟩
  have hv' := hv
  obtain ⟨-, hwL, hΔ, -⟩ := hv'
  obtain ⟨e1, e2, hi⟩ := flat8 (bS8_lt A) (jS8_lt A)
  obtain ⟨Dig, h1, h2⟩ := hB _ hi
  rw [e1, e2] at h2
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hzv := ZMod.val_lt (Multiplicative.toAdd z)
  obtain ⟨j, hj⟩ : ∃ j, j = (Multiplicative.toAdd z).val := ⟨_, rfl⟩
  have hjN : j < P.N := by rw [hN, hj]; exact hzv
  have hw : 1 ≤ P.w := by omega
  have h2w : (2 : ℕ) ≤ 2 ^ P.w := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ P.w := Nat.pow_le_pow_right (by norm_num) hw
  have hnw : n < 2 ^ P.w := by
    have := hv.2.2.2.2.2.2.2.1
    have h3 : 2 ^ (P.w - 1) ≤ 2 ^ P.w := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hnP]; omega
  have h0 : (0 : ℕ) = pkF P.w (fun _ => 0) P.N := by rw [pkF_const]; simp
  have hb := batch_sound P hv hO hlt (ta := fun _ => 1) (tb := fun _ => 0) (tc := fun _ => 0) (td := fun _ => 0)
    (tz := fun j => j % n) hO h0 h0 h0 hRZ
    (fun j _ => ⟨by omega, by positivity, by positivity, by positivity, by
      have := Nat.mod_lt j hn0; omega⟩) h1 j hjN
  obtain ⟨hdg, -, -, mz, -, -⟩ := hb
  refine ⟨digit (fld P.w Dig j), hdg, ?_⟩
  obtain ⟨-, -, -, -, ez⟩ := semN_rep (p := 2) (n := n) sZ invAt hrep₁ _ P.L (le_refl _) hdg
  rw [hnP] at mz
  have Wz : (wordG sZ invAt (digit (fld P.w Dig j)) P.L).2 = z := by
    apply Multiplicative.toAdd.injective
    rw [← ez, cast_of_modEq mz, Nat.mod_eq_of_lt (by rw [hj]; exact hzv), hj, ZMod.natCast_zmod_val]
  rw [wordX_pair]
  refine Prod.ext ?_ (word_const8 s2 invAt P hw16 hwL hΔ hO hrep₂ A h2 hjN)
  show wordX (fun u => (sZ u).2) invAt (digit (fld P.w Dig j)) P.L = z
  rw [← Wz, ← wordX_wordG]
  exact (wordX_map sZ invAt (MonoidHom.snd _ _) _ _).symm

theorem card_Z_SL8 {n : ℕ} [NeZero n] :
    Fintype.card (Multiplicative (ZMod n) × SpecialLinearGroup (Fin 2) GF8) = n * 504 := by
  rw [Fintype.card_prod, Fintype.card_multiplicative, ZMod.card, card_SL8]

end BipartiteDD.LeanAll.HaarGF8Z
