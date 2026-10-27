import BipartiteDD.LeanAll.HexGen
import BipartiteDD.LeanAll.GF9

/-! # A `HexGen.Coder` for `GF(9)`

Vectors of `GF(9)⁷` are written in base 9 with digit `a₀ + 3a₁` for `a₀ + a₁x` modulo `x² + 1` (the coordinates of
research/d13D7/hexgen2.c for `q = 9`). The checks use `GF9.addC`, `negC`, `mulC` on digits. -/

namespace BipartiteDD.LeanAll.HexGF9

open BipartiteDD BipartiteDD.Hexagon BipartiteDD.LeanAll.HexArith BipartiteDD.LeanAll.Orbit2
open BipartiteDD.LeanAll.HexLocal BipartiteDD.LeanAll.HexGen BipartiteDD.LeanAll.GF9
open Submodule

instance : Nontrivial GF9 := ⟨⟨0, 1, by decide⟩⟩

instance : IsDomain GF9 := NoZeroDivisors.to_isDomain GF9

noncomputable instance : Field GF9 := Fintype.fieldOfDomain GF9

theorem card_GF9 : Fintype.card GF9 = 9 := Fintype.card_fin 9

theorem code_add : ∀ x y : GF9, code (x + y) = addC (code x) (code y) := by decide
theorem code_sub : ∀ x y : GF9, code (x - y) = addC (code x) (negC (code y)) := by decide
theorem code_mul : ∀ x y : GF9, code (x * y) = mulC (code x) (code y) := by decide
theorem code_sq : ∀ x : GF9, code (x ^ 2) = mulC (code x) (code x) := by decide
theorem code_two : code (2 : GF9) = 2 := by decide
theorem code_zero : code (0 : GF9) = 0 := rfl

theorem eq_zero_iff {x : GF9} : x = 0 ↔ code x = 0 := ⟨fun h => h ▸ rfl, fun h => code_inj h⟩

/-- The vector of a base-9 number. -/
def vec9 (c : ℕ) : V7 GF9 := fun i => mk (cd 9 c i.val)

theorem code_vec9 (c : ℕ) (i : Fin 7) : code (vec9 c i) = cd 9 c i.val := code_mk (cd_lt (by norm_num) _ _)

/-- `Q(x) = 0`. -/
def qN9 (c : ℕ) : Bool :=
  Nat.beq (addC (addC (addC (mulC (cd 9 c 0) (cd 9 c 4)) (mulC (cd 9 c 1) (cd 9 c 5)))
    (mulC (cd 9 c 2) (cd 9 c 6))) (negC (mulC (cd 9 c 3) (cd 9 c 3)))) 0

theorem qN9_spec {c : ℕ} (h : qN9 c = true) : Qf (vec9 c) = 0 := by
  rw [eq_zero_iff]
  simp only [Qf, code_sub, code_add, code_mul, code_sq, code_vec9]
  simpa [qN9] using h

/-- `B(x, y) = 0`. -/
def bN9 (a b : ℕ) : Bool :=
  Nat.beq (addC (addC (addC (addC (addC (addC (mulC (cd 9 a 0) (cd 9 b 4)) (mulC (cd 9 a 4) (cd 9 b 0)))
    (mulC (cd 9 a 1) (cd 9 b 5))) (mulC (cd 9 a 5) (cd 9 b 1))) (mulC (cd 9 a 2) (cd 9 b 6)))
    (mulC (cd 9 a 6) (cd 9 b 2))) (negC (mulC 2 (mulC (cd 9 a 3) (cd 9 b 3))))) 0

theorem bN9_spec {a b : ℕ} (h : bN9 a b = true) : Bf (vec9 a) (vec9 b) = 0 := by
  rw [Bf, eq_zero_iff]
  simp only [code_sub, code_add, code_mul, code_two, code_vec9]
  simpa [bN9] using h

/-- `x_i y_j - x_j y_i`. -/
def plN9 (a b i j : ℕ) : ℕ := addC (mulC (cd 9 a i) (cd 9 b j)) (negC (mulC (cd 9 a j) (cd 9 b i)))

theorem code_pl (a b : ℕ) (i j : Fin 7) : code (pl (vec9 a) (vec9 b) i j) = plN9 a b i.val j.val := by
  simp only [pl, code_sub, code_mul, code_vec9, plN9]

/-- Tits' six equations. -/
def tN9 (a b : ℕ) : Bool :=
  Nat.beq (plN9 a b 1 2) (plN9 a b 3 4) && Nat.beq (plN9 a b 5 4) (plN9 a b 3 2) &&
  Nat.beq (plN9 a b 2 0) (plN9 a b 3 5) && Nat.beq (plN9 a b 6 5) (plN9 a b 3 0) &&
  Nat.beq (plN9 a b 0 1) (plN9 a b 3 6) && Nat.beq (plN9 a b 4 6) (plN9 a b 3 1)

theorem pl_eq {a b : ℕ} {i j k l : Fin 7} (h : Nat.beq (plN9 a b i.val j.val) (plN9 a b k.val l.val) = true) :
    pl (vec9 a) (vec9 b) i j = pl (vec9 a) (vec9 b) k l := by
  apply code_inj
  rw [code_pl, code_pl]
  simpa using h

theorem tN9_spec {a b : ℕ} (h : tN9 a b = true) : Tits (vec9 a) (vec9 b) := by
  simp only [tN9, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨pl_eq (i := 1) (j := 2) (k := 3) (l := 4) h1, pl_eq (i := 5) (j := 4) (k := 3) (l := 2) h2,
    pl_eq (i := 2) (j := 0) (k := 3) (l := 5) h3, pl_eq (i := 6) (j := 5) (k := 3) (l := 0) h4,
    pl_eq (i := 0) (j := 1) (k := 3) (l := 6) h5, pl_eq (i := 4) (j := 6) (k := 3) (l := 1) h6⟩

/-- The Plücker coordinates. -/
def plL9 (a b : ℕ) : List ℕ := pairs.map (fun ij => plN9 a b ij.1.val ij.2.val)

/-- Their base-9 number. -/
def plC9 (a b : ℕ) : ℕ := (plL9 a b).foldr (fun t acc => Nat.add t (Nat.mul 9 acc)) 0

theorem plL9_get (a b : ℕ) (k : Fin 21) :
    (plL9 a b).get ⟨k.val, by simp [plL9, pairs_length]⟩ = code (plV (vec9 a) (vec9 b) k) := by
  simp only [plL9, List.get_eq_getElem, List.getElem_map, plV]
  rw [code_pl]

theorem nrm_plV9 {a b : ℕ} (h : firstOneL (plL9 a b) = true) : Nrm (plV (vec9 a) (vec9 b)) := by
  obtain ⟨k, hk, h1, h0⟩ := firstOneL_spec _ h
  have hlen : (plL9 a b).length = 21 := by simp [plL9, pairs_length]
  refine ⟨⟨k, by omega⟩, ?_, fun j hj => ?_⟩
  · apply code_inj
    rw [← plL9_get]
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)] at h1
    simp only [List.get_eq_getElem, Option.getD_some] at h1 ⊢
    rw [h1]; rfl
  · apply code_inj
    rw [← plL9_get]
    have hj' : j.val < k := hj
    have := h0 j.val hj'
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)] at this
    simp only [List.get_eq_getElem, Option.getD_some] at this ⊢
    rw [this]; rfl

theorem plL9_eq {a b a' b' : ℕ} (h : plV (vec9 a) (vec9 b) = plV (vec9 a') (vec9 b')) : plL9 a b = plL9 a' b' := by
  have hlen : ∀ a b, (plL9 a b).length = 21 := fun a b => by simp [plL9, pairs_length]
  apply List.ext_get (by rw [hlen, hlen])
  intro k hk hk'
  have hk21 : k < 21 := by rw [hlen] at hk; exact hk
  have e1 := plL9_get a b ⟨k, hk21⟩
  have e2 := plL9_get a' b' ⟨k, hk21⟩
  rw [h, ← e2] at e1
  exact e1

/-- `y = α a + β b`. -/
def lin9 (y a b α β : ℕ) : Bool :=
  Nat.blt α 9 && Nat.blt β 9 &&
    allR (fun i => Nat.beq (cd 9 y i) (addC (mulC α (cd 9 a i)) (mulC β (cd 9 b i)))) 0 7

theorem lin9_spec {y a b α β : ℕ} (h : lin9 y a b α β = true) : vec9 y = mk α • vec9 a + mk β • vec9 b := by
  simp only [lin9, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨hα, hβ⟩, h⟩ := h
  funext i
  apply code_inj
  have h1 := allR_spec h i.val (Nat.zero_le _) (by have := i.isLt; omega)
  simp only [Nat.beq_eq] at h1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, code_add, code_mul, code_vec9, code_mk hα, code_mk hβ]
  exact h1

/-- A normalised point of the quadric. -/
def ptB9 (c : ℕ) : Bool := Nat.blt c (Nat.pow 9 7) && firstOne (cd 9 c) 0 7 && qN9 c

/-- A hexagon pair with normalised Plücker coordinates. -/
def lnB9 (a b : ℕ) : Bool := qN9 a && qN9 b && bN9 a b && tN9 a b && firstOneL (plL9 a b)

theorem nrm_vec9 {c : ℕ} (h : firstOne (cd 9 c) 0 7 = true) : Nrm (vec9 c) := by
  obtain ⟨j, -, hj, h1, h0⟩ := firstOne_spec _ 7 0 h
  refine ⟨⟨j, by omega⟩, ?_, fun j' hj' => ?_⟩
  · apply code_inj; rw [code_vec9]; exact h1
  · apply code_inj; rw [code_vec9]; exact h0 j'.val (Nat.zero_le _) hj'

/-- The coder. -/
noncomputable def coder : Coder GF9 where
  vec := vec9
  ptB := ptB9
  pt_nrm := fun c h => by
    simp only [ptB9, Bool.and_eq_true] at h; exact nrm_vec9 h.1.2
  pt_q := fun c h => by
    simp only [ptB9, Bool.and_eq_true] at h; exact qN9_spec h.2
  pt_inj := fun c c' h h' he => by
    simp only [ptB9, Bool.and_eq_true, Nat.blt_eq] at h h'
    refine eq_of_cd (by norm_num) 7 c c' h.1.1 h'.1.1 (fun i hi => ?_)
    have := congrArg code (congrFun he ⟨i, hi⟩)
    rwa [code_vec9, code_vec9] at this
  lnB := lnB9
  ln_pair := fun a b h => by
    simp only [lnB9, Bool.and_eq_true] at h
    exact ⟨qN9_spec h.1.1.1.1, qN9_spec h.1.1.1.2, bN9_spec h.1.1.2, tN9_spec h.1.2⟩
  ln_nrm := fun a b h => by
    simp only [lnB9, Bool.and_eq_true] at h; exact nrm_plV9 h.2
  plC := plC9
  pl_inj := fun a b a' b' h => by unfold plC9; rw [plL9_eq h]
  lin := lin9
  lin_mem := fun y a b α β h => by
    rw [lin9_spec h]; exact Submodule.mem_span_pair.2 ⟨mk α, mk β, rfl⟩

end BipartiteDD.LeanAll.HexGF9
