import BipartiteDD.LeanAll.HexGen
import BipartiteDD.LeanAll.GF8

/-! # A `HexGen.Coder` for `GF(8)`

Vectors of `GF(8)⁷` are written in base 8 with digit `a₀ + 2a₁ + 4a₂` for `a₀ + a₁x + a₂x²` modulo `x³ + x + 1`
(the coordinates of research/d10D7/hexgen2.c for `q = 8`). The checks use `xor` for sums and `GF8.mulC` for products;
in characteristic 2 every minus sign is a plus and `2 = 0`. -/

namespace BipartiteDD.LeanAll.HexGF8

open BipartiteDD BipartiteDD.Hexagon BipartiteDD.LeanAll.HexArith BipartiteDD.LeanAll.Orbit2
open BipartiteDD.LeanAll.HexLocal BipartiteDD.LeanAll.HexGen BipartiteDD.LeanAll.GF8
open Submodule

instance : Nontrivial GF8 := ⟨⟨0, 1, by decide⟩⟩

instance : IsDomain GF8 := NoZeroDivisors.to_isDomain GF8

noncomputable instance : Field GF8 := Fintype.fieldOfDomain GF8

theorem card_GF8 : Fintype.card GF8 = 8 := Fintype.card_fin 8

theorem code_add : ∀ x y : GF8, code (x + y) = Nat.xor (code x) (code y) := by decide
theorem code_sub : ∀ x y : GF8, code (x - y) = Nat.xor (code x) (code y) := by decide
theorem code_mul : ∀ x y : GF8, code (x * y) = mulC (code x) (code y) := by decide
theorem code_sq : ∀ x : GF8, code (x ^ 2) = mulC (code x) (code x) := by decide
theorem two_eq : (2 : GF8) = 0 := by decide
theorem code_zero : code (0 : GF8) = 0 := rfl
theorem code_one : code (1 : GF8) = 1 := rfl

theorem eq_zero_iff {x : GF8} : x = 0 ↔ code x = 0 := ⟨fun h => h ▸ rfl, fun h => code_inj h⟩

/-- The vector of a base-8 number. -/
def vec8 (c : ℕ) : V7 GF8 := fun i => mk (cd 8 c i.val)

theorem code_vec8 (c : ℕ) (i : Fin 7) : code (vec8 c i) = cd 8 c i.val := code_mk (cd_lt (by norm_num) _ _)

/-- `Q(x) = 0`. -/
def qN8 (c : ℕ) : Bool :=
  Nat.beq (Nat.xor (Nat.xor (Nat.xor (mulC (cd 8 c 0) (cd 8 c 4)) (mulC (cd 8 c 1) (cd 8 c 5)))
    (mulC (cd 8 c 2) (cd 8 c 6))) (mulC (cd 8 c 3) (cd 8 c 3))) 0

theorem qN8_spec {c : ℕ} (h : qN8 c = true) : Qf (vec8 c) = 0 := by
  rw [eq_zero_iff]
  simp only [Qf, code_sub, code_add, code_mul, code_sq, code_vec8]
  simpa [qN8] using h

/-- `B(x, y) = 0`. -/
def bN8 (a b : ℕ) : Bool :=
  Nat.beq (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (mulC (cd 8 a 0) (cd 8 b 4)) (mulC (cd 8 a 4) (cd 8 b 0)))
    (mulC (cd 8 a 1) (cd 8 b 5))) (mulC (cd 8 a 5) (cd 8 b 1))) (mulC (cd 8 a 2) (cd 8 b 6)))
    (mulC (cd 8 a 6) (cd 8 b 2))) 0

theorem bN8_spec {a b : ℕ} (h : bN8 a b = true) : Bf (vec8 a) (vec8 b) = 0 := by
  have h2 : ∀ x : GF8, 2 * x = 0 := fun x => by rw [two_eq, zero_mul]
  rw [Bf, h2, sub_zero, eq_zero_iff]
  simp only [code_add, code_mul, code_vec8]
  simpa [bN8] using h

/-- `x_i y_j - x_j y_i`. -/
def plN8 (a b i j : ℕ) : ℕ := Nat.xor (mulC (cd 8 a i) (cd 8 b j)) (mulC (cd 8 a j) (cd 8 b i))

theorem code_pl (a b : ℕ) (i j : Fin 7) : code (pl (vec8 a) (vec8 b) i j) = plN8 a b i.val j.val := by
  simp only [pl, code_sub, code_mul, code_vec8, plN8]

/-- Tits' six equations. -/
def tN8 (a b : ℕ) : Bool :=
  Nat.beq (plN8 a b 1 2) (plN8 a b 3 4) && Nat.beq (plN8 a b 5 4) (plN8 a b 3 2) &&
  Nat.beq (plN8 a b 2 0) (plN8 a b 3 5) && Nat.beq (plN8 a b 6 5) (plN8 a b 3 0) &&
  Nat.beq (plN8 a b 0 1) (plN8 a b 3 6) && Nat.beq (plN8 a b 4 6) (plN8 a b 3 1)

theorem pl_eq {a b : ℕ} {i j k l : Fin 7} (h : Nat.beq (plN8 a b i.val j.val) (plN8 a b k.val l.val) = true) :
    pl (vec8 a) (vec8 b) i j = pl (vec8 a) (vec8 b) k l := by
  apply code_inj
  rw [code_pl, code_pl]
  simpa using h

theorem tN8_spec {a b : ℕ} (h : tN8 a b = true) : Tits (vec8 a) (vec8 b) := by
  simp only [tN8, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨pl_eq (i := 1) (j := 2) (k := 3) (l := 4) h1, pl_eq (i := 5) (j := 4) (k := 3) (l := 2) h2,
    pl_eq (i := 2) (j := 0) (k := 3) (l := 5) h3, pl_eq (i := 6) (j := 5) (k := 3) (l := 0) h4,
    pl_eq (i := 0) (j := 1) (k := 3) (l := 6) h5, pl_eq (i := 4) (j := 6) (k := 3) (l := 1) h6⟩

/-- The Plücker coordinates. -/
def plL8 (a b : ℕ) : List ℕ := pairs.map (fun ij => plN8 a b ij.1.val ij.2.val)

/-- Their base-8 number. -/
def plC8 (a b : ℕ) : ℕ := (plL8 a b).foldr (fun t acc => Nat.add t (Nat.mul 8 acc)) 0

theorem plL8_get (a b : ℕ) (k : Fin 21) :
    (plL8 a b).get ⟨k.val, by simp [plL8, pairs_length]⟩ = code (plV (vec8 a) (vec8 b) k) := by
  simp only [plL8, List.get_eq_getElem, List.getElem_map, plV]
  rw [code_pl]

theorem nrm_plV8 {a b : ℕ} (h : firstOneL (plL8 a b) = true) : Nrm (plV (vec8 a) (vec8 b)) := by
  obtain ⟨k, hk, h1, h0⟩ := firstOneL_spec _ h
  have hlen : (plL8 a b).length = 21 := by simp [plL8, pairs_length]
  refine ⟨⟨k, by omega⟩, ?_, fun j hj => ?_⟩
  · apply code_inj
    rw [← plL8_get]
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)] at h1
    simp only [List.get_eq_getElem, Option.getD_some] at h1 ⊢
    rw [h1]; rfl
  · apply code_inj
    rw [← plL8_get]
    have hj' : j.val < k := hj
    have := h0 j.val hj'
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)] at this
    simp only [List.get_eq_getElem, Option.getD_some] at this ⊢
    rw [this]; rfl

theorem plL8_eq {a b a' b' : ℕ} (h : plV (vec8 a) (vec8 b) = plV (vec8 a') (vec8 b')) : plL8 a b = plL8 a' b' := by
  have hlen : ∀ a b, (plL8 a b).length = 21 := fun a b => by simp [plL8, pairs_length]
  apply List.ext_get (by rw [hlen, hlen])
  intro k hk hk'
  have hk21 : k < 21 := by rw [hlen] at hk; exact hk
  have e1 := plL8_get a b ⟨k, hk21⟩
  have e2 := plL8_get a' b' ⟨k, hk21⟩
  rw [h, ← e2] at e1
  exact e1

/-- `y = α a + β b`. -/
def lin8 (y a b α β : ℕ) : Bool :=
  Nat.blt α 8 && Nat.blt β 8 &&
    allR (fun i => Nat.beq (cd 8 y i) (Nat.xor (mulC α (cd 8 a i)) (mulC β (cd 8 b i)))) 0 7

theorem lin8_spec {y a b α β : ℕ} (h : lin8 y a b α β = true) : vec8 y = mk α • vec8 a + mk β • vec8 b := by
  simp only [lin8, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨hα, hβ⟩, h⟩ := h
  funext i
  apply code_inj
  have h1 := allR_spec h i.val (Nat.zero_le _) (by have := i.isLt; omega)
  simp only [Nat.beq_eq] at h1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, code_add, code_mul, code_vec8, code_mk hα, code_mk hβ]
  exact h1

/-- A normalised point of the quadric. -/
def ptB8 (c : ℕ) : Bool := Nat.blt c (Nat.pow 8 7) && firstOne (cd 8 c) 0 7 && qN8 c

/-- A hexagon pair with normalised Plücker coordinates. -/
def lnB8 (a b : ℕ) : Bool := qN8 a && qN8 b && bN8 a b && tN8 a b && firstOneL (plL8 a b)

theorem nrm_vec8 {c : ℕ} (h : firstOne (cd 8 c) 0 7 = true) : Nrm (vec8 c) := by
  obtain ⟨j, -, hj, h1, h0⟩ := firstOne_spec _ 7 0 h
  refine ⟨⟨j, by omega⟩, ?_, fun j' hj' => ?_⟩
  · apply code_inj; rw [code_vec8]; exact h1
  · apply code_inj; rw [code_vec8]; exact h0 j'.val (Nat.zero_le _) hj'

/-- The coder. -/
noncomputable def coder : Coder GF8 where
  vec := vec8
  ptB := ptB8
  pt_nrm := fun c h => by
    simp only [ptB8, Bool.and_eq_true] at h; exact nrm_vec8 h.1.2
  pt_q := fun c h => by
    simp only [ptB8, Bool.and_eq_true] at h; exact qN8_spec h.2
  pt_inj := fun c c' h h' he => by
    simp only [ptB8, Bool.and_eq_true, Nat.blt_eq] at h h'
    refine eq_of_cd (by norm_num) 7 c c' h.1.1 h'.1.1 (fun i hi => ?_)
    have := congrArg code (congrFun he ⟨i, hi⟩)
    rwa [code_vec8, code_vec8] at this
  lnB := lnB8
  ln_pair := fun a b h => by
    simp only [lnB8, Bool.and_eq_true] at h
    exact ⟨qN8_spec h.1.1.1.1, qN8_spec h.1.1.1.2, bN8_spec h.1.1.2, tN8_spec h.1.2⟩
  ln_nrm := fun a b h => by
    simp only [lnB8, Bool.and_eq_true] at h; exact nrm_plV8 h.2
  plC := plC8
  pl_inj := fun a b a' b' h => by unfold plC8; rw [plL8_eq h]
  lin := lin8
  lin_mem := fun y a b α β h => by
    rw [lin8_spec h]; exact Submodule.mem_span_pair.2 ⟨mk α, mk β, rfl⟩

end BipartiteDD.LeanAll.HexGF8
