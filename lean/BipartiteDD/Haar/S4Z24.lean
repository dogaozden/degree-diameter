import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic

/-! The group `S_4 × Z_24` of the (7,5) record on 1152 vertices, with a computable numbering of its
elements by `ℕ`.

The group is `Equiv.Perm (Fin 4) × Multiplicative (ZMod 24)`, with product `(f, c) * (h, d) = (f ∘ h, c + d)`.
A permutation `f` is written in one-line form `[f 0, f 1, f 2, f 3]`. `permTab p` lists the 24 one-line
forms in lexicographic order, `invTab p` the one-line forms of their inverses; `permOf p` is the
permutation they define. The element with index `n < 576` is `grpOf n = (permOf (n % 24), n / 24)`. -/

namespace BipartiteDD.Haar.S4Z24

/-- The group. -/
abbrev Grp : Type := Equiv.Perm (Fin 4) × Multiplicative (ZMod 24)

/-- The one-line forms of the 24 permutations of `Fin 4`, in lexicographic order. -/
def permTab : Fin 24 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![0, 1, 3, 2], ![0, 2, 1, 3], ![0, 2, 3, 1], ![0, 3, 1, 2], ![0, 3, 2, 1],
    ![1, 0, 2, 3], ![1, 0, 3, 2], ![1, 2, 0, 3], ![1, 2, 3, 0], ![1, 3, 0, 2], ![1, 3, 2, 0],
    ![2, 0, 1, 3], ![2, 0, 3, 1], ![2, 1, 0, 3], ![2, 1, 3, 0], ![2, 3, 0, 1], ![2, 3, 1, 0],
    ![3, 0, 1, 2], ![3, 0, 2, 1], ![3, 1, 0, 2], ![3, 1, 2, 0], ![3, 2, 0, 1], ![3, 2, 1, 0]]

/-- The one-line forms of the inverses of the permutations of `permTab`. -/
def invTab : Fin 24 → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3], ![0, 1, 3, 2], ![0, 2, 1, 3], ![0, 3, 1, 2], ![0, 2, 3, 1], ![0, 3, 2, 1],
    ![1, 0, 2, 3], ![1, 0, 3, 2], ![2, 0, 1, 3], ![3, 0, 1, 2], ![2, 0, 3, 1], ![3, 0, 2, 1],
    ![1, 2, 0, 3], ![1, 3, 0, 2], ![2, 1, 0, 3], ![3, 1, 0, 2], ![2, 3, 0, 1], ![3, 2, 0, 1],
    ![1, 2, 3, 0], ![1, 3, 2, 0], ![2, 1, 3, 0], ![3, 1, 2, 0], ![2, 3, 1, 0], ![3, 2, 1, 0]]

theorem invTab_permTab : ∀ (p : Fin 24) (i : Fin 4), invTab p (permTab p i) = i := by decide

theorem permTab_invTab : ∀ (p : Fin 24) (i : Fin 4), permTab p (invTab p i) = i := by decide

/-- The permutation with index `p`. -/
def permOf (p : Fin 24) : Equiv.Perm (Fin 4) where
  toFun := permTab p
  invFun := invTab p
  left_inv i := invTab_permTab p i
  right_inv i := permTab_invTab p i

theorem permOf_injective : Function.Injective permOf := by
  intro p q h
  have h' : ∀ i, permTab p i = permTab q i := fun i => congrArg (fun f => f i) h
  revert h'
  revert p q
  decide

theorem card_perm : Fintype.card (Equiv.Perm (Fin 4)) = 24 := by
  rw [Fintype.card_perm]
  rfl

theorem permOf_surjective : Function.Surjective permOf := by
  have h : Function.Bijective permOf := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨permOf_injective, by rw [card_perm]; rfl⟩
  exact h.2

theorem card_grp : Fintype.card Grp = 576 := by
  rw [Fintype.card_prod, card_perm, Fintype.card_multiplicative, ZMod.card]

/-- The element with index `n`, for `n < 576`: `(permOf (n % 24), n / 24)`. -/
def grpOf (n : ℕ) : Grp :=
  (permOf ⟨n % 24, Nat.mod_lt _ (by decide)⟩, Multiplicative.ofAdd ((n / 24 : ℕ) : ZMod 24))

/-- Every element has an index below 576. -/
theorem exists_grpOf (g : Grp) : ∃ n < 576, grpOf n = g := by
  obtain ⟨f, c⟩ := g
  obtain ⟨p, rfl⟩ := permOf_surjective f
  refine ⟨24 * c.toAdd.val + p.1, ?_, ?_⟩
  · have h1 : c.toAdd.val < 24 := ZMod.val_lt _
    have h2 := p.2
    omega
  · have hp : (24 * c.toAdd.val + p.1) % 24 = p.1 := by omega
    have hc : (24 * c.toAdd.val + p.1) / 24 = c.toAdd.val := by omega
    unfold grpOf
    simp only [hp, hc, ZMod.natCast_zmod_val]
    rfl

end BipartiteDD.Haar.S4Z24
