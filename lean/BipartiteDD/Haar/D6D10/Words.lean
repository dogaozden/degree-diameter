import BipartiteDD.Haar.D6D10.Cover
import BipartiteDD.Haar.PGL37Nat
import BipartiteDD.Haar.PGL37Z5

/-! The covering hypothesis of the (6,10) record, in `PGL(2, 37) × Z_5`.

`sel j` is the `j`-th element of the connection set. `wordG c` is the nine-letter alternating product of the code `c`
(`x₁ x₂⁻¹ x₃ x₄⁻¹ x₅ x₆⁻¹ x₇ x₈⁻¹ x₉`, written right-nested). `wordG_eq` identifies it with the element of index `n`
whenever the Nat check `okC c n` holds, and `cover` is the covering hypothesis of `Diam10`. -/

namespace BipartiteDD.Haar.D6D10

open BipartiteDD.Haar.PGL37

/-- The `j`-th element of the connection set, in `PGL(2, 37) × Z_5`. -/
def sel (j : ℕ) : PGL37Z5.Grp := (gM (sN j), Multiplicative.ofAdd (zN j : ZMod 5))

/-- The connection set. -/
def SS : Finset PGL37Z5.Grp := {sel 0, sel 1, sel 2, sel 3, sel 4, sel 5}

theorem card_SS : SS.card = 6 := by
  decide

theorem sel_mem (j : ℕ) (hj : j < 6) : sel j ∈ SS := by
  have h : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [SS]

theorem sN_ok : ∀ j : ℕ, j < 6 → detZ (sN j) ≠ 0 ∧ (sN j).2.1 < 37 ∧ (sN j).2.2.1 < 37 := by
  decide

theorem dig_lt (c k : ℕ) : dig c k < 6 := Nat.mod_lt _ (by norm_num)

theorem sN_det (c k : ℕ) : detZ (sN (dig c k)) ≠ 0 := (sN_ok _ (dig_lt c k)).1

theorem adjN_det (c k : ℕ) : detZ (adjN (sN (dig c k))) ≠ 0 := by
  rw [detZ_adjN _ (sN_ok _ (dig_lt c k)).2.1 (sN_ok _ (dig_lt c k)).2.2]
  exact sN_det c k

theorem Ls_ok (c : ℕ) : ∀ M ∈ Ls c, detZ M ≠ 0 := by
  intro M hM
  simp only [Ls, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hM
  rcases hM with h | h | h | h | h | h | h | h | h <;> subst h
  · exact sN_det c 0
  · exact adjN_det c 1
  · exact sN_det c 2
  · exact adjN_det c 3
  · exact sN_det c 4
  · exact adjN_det c 5
  · exact sN_det c 6
  · exact adjN_det c 7
  · exact sN_det c 8

theorem gM_adjN_dig (c k : ℕ) : gM (adjN (sN (dig c k))) = (gM (sN (dig c k)))⁻¹ :=
  gM_adjN _ (sN_det c k) (sN_ok _ (dig_lt c k)).2.1 (sN_ok _ (dig_lt c k)).2.2

/-- The nine-letter word of the code `c`, right-nested. -/
def wordG (c : ℕ) : PGL37Z5.Grp :=
  sel (dig c 0) * ((sel (dig c 1))⁻¹ * (sel (dig c 2) * ((sel (dig c 3))⁻¹ *
    (sel (dig c 4) * ((sel (dig c 5))⁻¹ * (sel (dig c 6) * ((sel (dig c 7))⁻¹ * sel (dig c 8))))))))

theorem wordG_fst (c : ℕ) : (wordG c).1 = gM (prodN (Ls c)) := by
  rw [gM_prodN _ (Ls_ok c)]
  simp only [wordG, sel, Prod.fst_mul, Prod.fst_inv, Ls, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, gM_adjN_dig]

theorem toAdd_mul' (x y : Multiplicative (ZMod 5)) :
    Multiplicative.toAdd (x * y) = Multiplicative.toAdd x + Multiplicative.toAdd y := rfl

theorem toAdd_inv' (x : Multiplicative (ZMod 5)) : Multiplicative.toAdd x⁻¹ = -Multiplicative.toAdd x := rfl

theorem toAdd_ofAdd' (a : ZMod 5) : Multiplicative.toAdd (Multiplicative.ofAdd a) = a := rfl

theorem wordG_eq (c n : ℕ) (hP : normN (prodN (Ls c)) = quadN (n / 5)) (hZ : zW c = n % 5) :
    wordG c = PGL37Z5.grpOf n := by
  have hdet : detZ (prodN (Ls c)) ≠ 0 := detZ_prodN _ (Ls_ok c)
  have h1 : (wordG c).1 = PGL37.grpOf (n / 5) := by
    rw [wordG_fst c, ← gM_normN _ hdet, hP]
    rfl
  have hz : Multiplicative.toAdd (wordG c).2 = ((zW c : ℕ) : ZMod 5) := by
    unfold wordG sel
    simp only [Prod.snd_mul, Prod.snd_inv, toAdd_mul', toAdd_inv', toAdd_ofAdd']
    unfold zW
    rw [ZMod.natCast_mod]
    push_cast
    have h4 : (4 : ZMod 5) = -1 := by decide
    rw [h4]
    ring
  have h2 : (wordG c).2 = Multiplicative.ofAdd ((n % 5 : ℕ) : ZMod 5) := by
    rw [show (wordG c).2 = Multiplicative.ofAdd (Multiplicative.toAdd (wordG c).2) from rfl, hz, hZ]
  exact Prod.ext h1 h2

theorem cover : ∀ g : PGL37Z5.Grp, ∃ x₁ ∈ SS, ∃ x₂ ∈ SS, ∃ x₃ ∈ SS, ∃ x₄ ∈ SS, ∃ x₅ ∈ SS, ∃ x₆ ∈ SS,
    ∃ x₇ ∈ SS, ∃ x₈ ∈ SS, ∃ x₉ ∈ SS,
    g = x₁ * (x₂⁻¹ * (x₃ * (x₄⁻¹ * (x₅ * (x₆⁻¹ * (x₇ * (x₈⁻¹ * x₉))))))) := by
  intro g
  obtain ⟨c, hc⟩ := exC (PGL37Z5.enc g) (PGL37Z5.enc_lt g)
  obtain ⟨hP, hZ⟩ := okC_spec hc
  refine ⟨sel (dig c 0), sel_mem _ (dig_lt c 0), sel (dig c 1), sel_mem _ (dig_lt c 1),
    sel (dig c 2), sel_mem _ (dig_lt c 2), sel (dig c 3), sel_mem _ (dig_lt c 3),
    sel (dig c 4), sel_mem _ (dig_lt c 4), sel (dig c 5), sel_mem _ (dig_lt c 5),
    sel (dig c 6), sel_mem _ (dig_lt c 6), sel (dig c 7), sel_mem _ (dig_lt c 7),
    sel (dig c 8), sel_mem _ (dig_lt c 8), ?_⟩
  exact (PGL37Z5.grpOf_enc g).symm.trans (wordG_eq c _ hP hZ).symm

end BipartiteDD.Haar.D6D10
