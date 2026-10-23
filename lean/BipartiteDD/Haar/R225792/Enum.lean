import BipartiteDD.Haar.R225792.Lists
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod

/-! The enumerations of the factors of `G8 = PSL(2,7) × SL(2,7) × Z/2` by `Fin 168`, `Fin 336`, `Fin 2`, and
the equivalence `G8 ⊕ G8 ≃ Fin 225792`. Surjectivity and injectivity are checked by the kernel on the explicit
lists of `Lists.lean`. -/

namespace BipartiteDD.Haar.R225792

open M2

/-- The `i`-th canonical PSL representative. -/
def pslAt (i : Fin 168) : M2 := pslList.getD i.val default

/-- The `j`-th element of SL(2,7). -/
def slAt (j : Fin 336) : M2 := slList.getD j.val default

theorem pslAt_spec : ∀ i : Fin 168, (pslAt i).det = 1 ∧ canon (pslAt i) = pslAt i := by
  decide +kernel

theorem slAt_spec : ∀ j : Fin 336, (slAt j).det = 1 := by
  decide +kernel

theorem pslAt_inj : ∀ i j : Fin 168, pslAt i = pslAt j → i = j := by
  decide +kernel

theorem slAt_inj : ∀ i j : Fin 336, slAt i = slAt j → i = j := by
  decide +kernel

/-- Every canonical PSL matrix is listed. -/
theorem pslAt_surj : ∀ a b c d : ZMod 7,
    ((M2.mk a b c d).det = 1 ∧ canon (M2.mk a b c d) = M2.mk a b c d) →
      ∃ i : Fin 168, pslAt i = M2.mk a b c d := by
  decide +kernel

/-- Every matrix of determinant `1` is listed. -/
theorem slAt_surj : ∀ a b c d : ZMod 7,
    (M2.mk a b c d).det = 1 → ∃ j : Fin 336, slAt j = M2.mk a b c d := by
  decide +kernel

theorem fZ_inj : ∀ i j : Fin 2,
    Multiplicative.ofAdd ((i.val : ℕ) : ZMod 2) = Multiplicative.ofAdd ((j.val : ℕ) : ZMod 2) → i = j := by
  decide +kernel

theorem fZ_surj : ∀ z : ZMod 2, ∃ k : Fin 2, Multiplicative.ofAdd ((k.val : ℕ) : ZMod 2) = Multiplicative.ofAdd z := by
  decide +kernel

/-- The PSL element with index `i`. -/
def fP (i : Fin 168) : PSL := ⟨pslAt i, pslAt_spec i⟩

/-- The SL element with index `j`. -/
def fS (j : Fin 336) : SL := ⟨slAt j, slAt_spec j⟩

/-- The Z/2 element with index `z`. -/
def fZ (z : Fin 2) : Multiplicative (ZMod 2) := Multiplicative.ofAdd ((z.val : ℕ) : ZMod 2)

theorem fP_surj (x : PSL) : ∃ i, fP i = x := by
  obtain ⟨⟨a, b, c, d⟩, hx⟩ := x
  obtain ⟨i, hi⟩ := pslAt_surj a b c d hx
  exact ⟨i, Subtype.ext hi⟩

theorem fS_surj (x : SL) : ∃ j, fS j = x := by
  obtain ⟨⟨a, b, c, d⟩, hx⟩ := x
  obtain ⟨j, hj⟩ := slAt_surj a b c d hx
  exact ⟨j, Subtype.ext hj⟩

/-- The PSL factor as an equivalence with `Fin 168`. -/
noncomputable def eP : Fin 168 ≃ PSL :=
  Equiv.ofBijective fP ⟨fun i j h => pslAt_inj i j (congrArg Subtype.val h), fP_surj⟩

/-- The SL factor as an equivalence with `Fin 336`. -/
noncomputable def eS : Fin 336 ≃ SL :=
  Equiv.ofBijective fS ⟨fun i j h => slAt_inj i j (congrArg Subtype.val h), fS_surj⟩

/-- The Z/2 factor as an equivalence with `Fin 2`. -/
noncomputable def eZ : Fin 2 ≃ Multiplicative (ZMod 2) :=
  Equiv.ofBijective fZ ⟨fun i j h => fZ_inj i j h, fun b => by
    obtain ⟨k, hk⟩ := fZ_surj (Multiplicative.toAdd b)
    exact ⟨k, hk⟩⟩

/-- `G8 ≃ Fin 112896`. -/
noncomputable def eG : G8 ≃ Fin 112896 :=
  ((Equiv.prodCongr eP (Equiv.prodCongr eS eZ)).symm.trans
    (Equiv.prodCongr (Equiv.refl (Fin 168)) finProdFinEquiv)).trans
    (finProdFinEquiv.trans (finCongr (by norm_num)))

/-- The two sides of the Haar graph on `G8`, numbered `0 … 225791`. -/
noncomputable def e2 : G8 ⊕ G8 ≃ Fin 225792 :=
  (Equiv.sumCongr eG eG).trans (finSumFinEquiv.trans (finCongr (by norm_num)))

end BipartiteDD.Haar.R225792
