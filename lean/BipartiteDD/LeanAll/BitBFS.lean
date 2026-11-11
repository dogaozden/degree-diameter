import BipartiteDD.HexagonD7.Defs
import Mathlib.Data.Nat.Bitwise

/-! # Same-side distances by layered bit sets

For a bipartite graph with sides `S` (`KS` vertices) and `O` (`KO` vertices) given by neighbour lists, layer `t` of a
breadth-first search from all of `S` at once is a number per vertex whose bit `s` says that source `s` reaches the
vertex in at most `t` steps. Layer 1 is computed from the lists (`orL unit`); layers 2 to 5 are data, each checked
against the layer before it (`layOK`: every bit comes from a neighbour); the last check (`finOK`) asks every
`S`-vertex to see all of `S` from its neighbours in layer 5. `reach6`: all pairs of `S`-vertices are within 6. -/

namespace BipartiteDD.LeanAll.BitBFS

open BipartiteDD.HexagonD7

/-- The `or` of `f y` over `y ∈ l`. -/
def orL (f : ℕ → ℕ) : List ℕ → ℕ
  | [] => 0
  | y :: l => Nat.lor (f y) (orL f l)

theorem testBit_orL {f : ℕ → ℕ} {s : ℕ} : ∀ {l : List ℕ}, (orL f l).testBit s = true → ∃ y ∈ l, (f y).testBit s = true
  | [], h => by simp [orL] at h
  | y :: l, h => by
    simp only [orL] at h
    have : (Nat.lor (f y) (orL f l)).testBit s = ((f y).testBit s || (orL f l).testBit s) := Nat.testBit_lor _ _ _
    rw [this, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨y, List.mem_cons_self .., h⟩
    · obtain ⟨z, hz, h'⟩ := testBit_orL h
      exact ⟨z, List.mem_cons_of_mem _ hz, h'⟩

/-- The number with the single bit `y`. -/
def unit (y : ℕ) : ℕ := Nat.shiftLeft 1 y

theorem testBit_unit {y s : ℕ} (h : (unit y).testBit s = true) : s = y := by
  have e : unit y = 2 ^ y := Nat.one_shiftLeft y
  rw [e, Nat.testBit_two_pow] at h
  exact (of_decide_eq_true h).symm

/-- Every bit of `Lt x` is a bit of `Lp y` for a neighbour `y` of `x`. -/
def layOK (Lt Lp : ℕ → ℕ) (nb : ℕ → List ℕ) (x : ℕ) : Bool :=
  Nat.beq (Nat.lor (Lt x) (orL Lp (nb x))) (orL Lp (nb x))

theorem layOK_spec {Lt Lp : ℕ → ℕ} {nb : ℕ → List ℕ} {x s : ℕ} (h : layOK Lt Lp nb x = true)
    (hs : (Lt x).testBit s = true) : ∃ y ∈ nb x, (Lp y).testBit s = true := by
  have e := Nat.eq_of_beq_eq_true h
  apply testBit_orL
  rw [← e]
  have : (Nat.lor (Lt x) (orL Lp (nb x))).testBit s = ((Lt x).testBit s || (orL Lp (nb x)).testBit s) :=
    Nat.testBit_lor _ _ _
  rw [this, hs, Bool.true_or]

/-- The neighbours of `x` see all of `0, …, K - 1` in `Lp`. -/
def finOK (K : ℕ) (Lp : ℕ → ℕ) (nb : ℕ → List ℕ) (x : ℕ) : Bool :=
  Nat.beq (orL Lp (nb x)) (Nat.sub (Nat.pow 2 K) 1)

theorem finOK_spec {K : ℕ} {Lp : ℕ → ℕ} {nb : ℕ → List ℕ} {x : ℕ} (h : finOK K Lp nb x = true) {s : ℕ} (hs : s < K) :
    ∃ y ∈ nb x, (Lp y).testBit s = true := by
  apply testBit_orL
  rw [Nat.eq_of_beq_eq_true h]
  show (2 ^ K - 1).testBit s = true
  rw [Nat.testBit_two_pow_sub_one]
  exact decide_eq_true hs

section Graph

variable {W : Type*} (G : SimpleGraph W) {KS : ℕ} (vS : Fin KS → W)

/-- Bit `s` of `f x` means: `s` is a source and reaches `x` in at most `t` steps. -/
def Sound {KX : ℕ} (vX : Fin KX → W) (f : ℕ → ℕ) (t : ℕ) : Prop :=
  ∀ x (hx : x < KX) s, (f x).testBit s = true → ∃ hs : s < KS, Reach G (vS ⟨s, hs⟩) (vX ⟨x, hx⟩) t

variable {G vS}

theorem Sound.step {KX KY t : ℕ} {vX : Fin KX → W} {vY : Fin KY → W} {nb : ℕ → List ℕ}
    (hadj : ∀ x (hx : x < KX), ∀ y ∈ nb x, ∃ hy : y < KY, G.Adj (vY ⟨y, hy⟩) (vX ⟨x, hx⟩))
    {Lt Lp : ℕ → ℕ} (hl : ∀ x < KX, layOK Lt Lp nb x = true) (ih : Sound G vS vY Lp t) :
    Sound G vS vX Lt (t + 1) := by
  intro x hx s hs
  obtain ⟨y, hy, hys⟩ := layOK_spec (hl x hx) hs
  obtain ⟨hyK, ha⟩ := hadj x hx y hy
  obtain ⟨hsK, hr⟩ := ih y hyK s hys
  exact ⟨hsK, hr.trans (Reach.adj ha)⟩

theorem sound_one {KY : ℕ} {vY : Fin KY → W} {nb : ℕ → List ℕ}
    (hadj : ∀ y (hy : y < KY), ∀ x ∈ nb y, ∃ hx : x < KS, G.Adj (vS ⟨x, hx⟩) (vY ⟨y, hy⟩)) :
    Sound G vS vY (fun y => orL unit (nb y)) 1 := by
  intro y hy s hs
  obtain ⟨x, hx, hxs⟩ := testBit_orL hs
  obtain rfl := testBit_unit hxs
  obtain ⟨hsK, ha⟩ := hadj y hy s hx
  exact ⟨hsK, Reach.adj ha⟩

/-- **Same-side distances.** -/
theorem reach6 {KO : ℕ} (vO : Fin KO → W) (nbS nbO : ℕ → List ℕ)
    (hSO : ∀ x (hx : x < KS), ∀ y ∈ nbS x, ∃ hy : y < KO, G.Adj (vO ⟨y, hy⟩) (vS ⟨x, hx⟩))
    (hOS : ∀ y (hy : y < KO), ∀ x ∈ nbO y, ∃ hx : x < KS, G.Adj (vS ⟨x, hx⟩) (vO ⟨y, hy⟩))
    (L2 L3 L4 L5 : ℕ → ℕ)
    (h2 : ∀ x < KS, layOK L2 (fun y => orL unit (nbO y)) nbS x = true)
    (h3 : ∀ y < KO, layOK L3 L2 nbO y = true) (h4 : ∀ x < KS, layOK L4 L3 nbS x = true)
    (h5 : ∀ y < KO, layOK L5 L4 nbO y = true) (h6 : ∀ x < KS, finOK KS L5 nbS x = true) :
    ∀ v v' : Fin KS, Reach G (vS v) (vS v') 6 := by
  have s1 := sound_one (G := G) (vS := vS) hOS
  have s2 := Sound.step hSO h2 s1
  have s3 := Sound.step hOS h3 s2
  have s4 := Sound.step hSO h4 s3
  have s5 := Sound.step hOS h5 s4
  intro v v'
  obtain ⟨y, hy, hys⟩ := finOK_spec (h6 v.val v.isLt) v'.isLt
  obtain ⟨hyK, ha⟩ := hSO v.val v.isLt y hy
  obtain ⟨_, hr⟩ := s5 y hyK v'.val hys
  exact Reach.symm (Reach.trans hr (Reach.adj ha))

end Graph

end BipartiteDD.LeanAll.BitBFS
