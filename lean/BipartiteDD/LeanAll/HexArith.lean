import BipartiteDD.Hexagon.Defs
import BipartiteDD.LeanAll.Orbit2

/-! # Vectors of `F_p^7` as natural numbers, for the local checks in `H(p)`

A vector of `F_p^7` is written as the base-`p` number `c = Σ cᵢ pⁱ` (the point codes of research/d10D7/hexgen2.c).
The checks below are Boolean functions on such numbers, built from `Nat` operations only so that the kernel evaluates
them directly; each has a lemma that turns a passing check into a statement in `ZMod p`:

* `qN`: `Q(x) = 0`; `bN`: `B(x, y) = 0`; `tN`: Tits' six equations; `linN`: `y = α x + β z`;
* `firstOne`: the first nonzero coordinate is `1` (normalised vectors, and normalised Plücker coordinates);
* `plL`: the 21 Plücker coordinates `x_i y_j - x_j y_i` (`i < j`), `plCode` their base-`p` number. -/

namespace BipartiteDD.LeanAll.HexArith

open BipartiteDD.Hexagon BipartiteDD.LeanAll.Orbit2

/-! ## Coordinates -/

/-- Coordinate `i` of the base-`p` number `c`. -/
def cd (p c i : ℕ) : ℕ := Nat.mod (Nat.div c (Nat.pow p i)) p

theorem cd_eq (p c i : ℕ) : cd p c i = c / p ^ i % p := rfl

theorem cd_lt {p : ℕ} (hp : 0 < p) (c i : ℕ) : cd p c i < p := Nat.mod_lt _ hp

/-- The vector of `c`. -/
def vec (p c : ℕ) : V7 (ZMod p) := fun i => ((cd p c i.val : ℕ) : ZMod p)

theorem cd_zero (p c : ℕ) : cd p c 0 = c % p := by simp [cd_eq]

theorem cd_succ (p c i : ℕ) : cd p c (i + 1) = cd p (c / p) i := by
  simp only [cd_eq, Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]

/-- Two numbers below `p ^ k` with the same first `k` digits are equal. -/
theorem eq_of_cd {p : ℕ} (hp : 0 < p) : ∀ k c c', c < p ^ k → c' < p ^ k →
    (∀ i < k, cd p c i = cd p c' i) → c = c' := by
  intro k
  induction k with
  | zero => intro c c' h h' _; simp at h h'; omega
  | succ k ih =>
    intro c c' h h' hd
    have h0 := hd 0 (by omega)
    rw [cd_zero, cd_zero] at h0
    have hq : c / p = c' / p := by
      refine ih _ _ ?_ ?_ (fun i hi => ?_)
      · rw [Nat.div_lt_iff_lt_mul hp, ← pow_succ]; exact h
      · rw [Nat.div_lt_iff_lt_mul hp, ← pow_succ]; exact h'
      · have := hd (i + 1) (by omega)
        rwa [cd_succ, cd_succ] at this
    rw [← Nat.div_add_mod c p, ← Nat.div_add_mod c' p, hq, h0]

variable {p : ℕ} [hp : Fact p.Prime]

theorem natCast_eq_of_mod {a b : ℕ} (h : a % p = b % p) : (a : ZMod p) = (b : ZMod p) :=
  (ZMod.natCast_eq_natCast_iff' a b p).2 h

theorem vec_apply (c : ℕ) (i : Fin 7) : vec p c i = ((cd p c i.val : ℕ) : ZMod p) := rfl

/-- Equal vectors have equal digits. -/
theorem cd_eq_of_vec {c c' : ℕ} (h : vec p c = vec p c') (i : ℕ) (hi : i < 7) : cd p c i = cd p c' i := by
  have h1 := congrFun h ⟨i, hi⟩
  simp only [vec] at h1
  have h2 := (ZMod.natCast_eq_natCast_iff' _ _ p).1 h1
  rwa [Nat.mod_eq_of_lt (cd_lt hp.out.pos _ _), Nat.mod_eq_of_lt (cd_lt hp.out.pos _ _)] at h2

theorem eq_of_vec {c c' : ℕ} (hc : c < p ^ 7) (hc' : c' < p ^ 7) (h : vec p c = vec p c') : c = c' :=
  eq_of_cd hp.out.pos 7 c c' hc hc' (fun i hi => cd_eq_of_vec h i hi)

/-! ## The quadric, its polar form, Tits' equations -/

/-- `Q(x) = x₀x₄ + x₁x₅ + x₂x₆ - x₃²` vanishes. -/
def qN (p c : ℕ) : Bool :=
  Nat.beq (Nat.mod (Nat.add (Nat.add (Nat.mul (cd p c 0) (cd p c 4)) (Nat.mul (cd p c 1) (cd p c 5)))
    (Nat.mul (cd p c 2) (cd p c 6))) p) (Nat.mod (Nat.mul (cd p c 3) (cd p c 3)) p)

theorem qN_spec {c : ℕ} (h : qN p c = true) : Qf (vec p c) = 0 := by
  simp only [qN, Nat.beq_eq] at h
  have h2 : (cd p c 0 * cd p c 4 + cd p c 1 * cd p c 5 + cd p c 2 * cd p c 6) % p = (cd p c 3 * cd p c 3) % p := h
  have h' := natCast_eq_of_mod (p := p) h2
  push_cast at h'
  simp only [Qf, vec_apply]
  change (↑(cd p c 0) * ↑(cd p c 4) + ↑(cd p c 1) * ↑(cd p c 5) + ↑(cd p c 2) * ↑(cd p c 6) -
    (↑(cd p c 3) : ZMod p) ^ 2 = 0)
  rw [h']; ring

/-- `B(x, y) = 0`. -/
def bN (p a b : ℕ) : Bool :=
  Nat.beq (Nat.mod (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul (cd p a 0) (cd p b 4))
    (Nat.mul (cd p a 4) (cd p b 0))) (Nat.mul (cd p a 1) (cd p b 5))) (Nat.mul (cd p a 5) (cd p b 1)))
    (Nat.mul (cd p a 2) (cd p b 6))) (Nat.mul (cd p a 6) (cd p b 2))) p)
    (Nat.mod (Nat.mul 2 (Nat.mul (cd p a 3) (cd p b 3))) p)

theorem bN_spec {a b : ℕ} (h : bN p a b = true) : Bf (vec p a) (vec p b) = 0 := by
  simp only [bN, Nat.beq_eq] at h
  have h2 : (cd p a 0 * cd p b 4 + cd p a 4 * cd p b 0 + cd p a 1 * cd p b 5 + cd p a 5 * cd p b 1 +
      cd p a 2 * cd p b 6 + cd p a 6 * cd p b 2) % p = (2 * (cd p a 3 * cd p b 3)) % p := h
  have h' := natCast_eq_of_mod (p := p) h2
  push_cast at h'
  simp only [Bf, vec_apply]
  change (↑(cd p a 0) * ↑(cd p b 4) + ↑(cd p a 4) * ↑(cd p b 0) + ↑(cd p a 1) * ↑(cd p b 5) +
    ↑(cd p a 5) * ↑(cd p b 1) + ↑(cd p a 2) * ↑(cd p b 6) + ↑(cd p a 6) * ↑(cd p b 2) -
    2 * ((↑(cd p a 3) : ZMod p) * ↑(cd p b 3)) = 0)
  rw [h']; ring

/-- One of Tits' equations, `p_ij = p_kl`, as `x_i y_j + x_l y_k ≡ x_k y_l + x_j y_i`. -/
def t1 (p a b i j k l : ℕ) : Bool :=
  Nat.beq (Nat.mod (Nat.add (Nat.mul (cd p a i) (cd p b j)) (Nat.mul (cd p a l) (cd p b k))) p)
    (Nat.mod (Nat.add (Nat.mul (cd p a k) (cd p b l)) (Nat.mul (cd p a j) (cd p b i))) p)

theorem t1_spec {a b : ℕ} {i j k l : Fin 7} (h : t1 p a b i.val j.val k.val l.val = true) :
    pl (vec p a) (vec p b) i j = pl (vec p a) (vec p b) k l := by
  simp only [t1, Nat.beq_eq] at h
  have h2 : (cd p a i.val * cd p b j.val + cd p a l.val * cd p b k.val) % p =
      (cd p a k.val * cd p b l.val + cd p a j.val * cd p b i.val) % p := h
  have h' := natCast_eq_of_mod (p := p) h2
  push_cast at h'
  simp only [pl, vec_apply]
  linear_combination h'

/-- Tits' six equations. -/
def tN (p a b : ℕ) : Bool :=
  t1 p a b 1 2 3 4 && t1 p a b 5 4 3 2 && t1 p a b 2 0 3 5 && t1 p a b 6 5 3 0 && t1 p a b 0 1 3 6 &&
    t1 p a b 4 6 3 1

theorem tN_spec {a b : ℕ} (h : tN p a b = true) : Tits (vec p a) (vec p b) := by
  simp only [tN, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨t1_spec (i := 1) (j := 2) (k := 3) (l := 4) h1, t1_spec (i := 5) (j := 4) (k := 3) (l := 2) h2,
    t1_spec (i := 2) (j := 0) (k := 3) (l := 5) h3, t1_spec (i := 6) (j := 5) (k := 3) (l := 0) h4,
    t1_spec (i := 0) (j := 1) (k := 3) (l := 6) h5, t1_spec (i := 4) (j := 6) (k := 3) (l := 1) h6⟩

/-! ## Linear combinations -/

/-- `y = α a + β b`, coordinatewise mod `p`. -/
def linN (p y a b α β : ℕ) : Bool :=
  allR (fun i => Nat.beq (cd p y i) (Nat.mod (Nat.add (Nat.mul α (cd p a i)) (Nat.mul β (cd p b i))) p)) 0 7

theorem linN_spec {y a b α β : ℕ} (h : linN p y a b α β = true) :
    vec p y = (α : ZMod p) • vec p a + (β : ZMod p) • vec p b := by
  funext i
  have h1 := allR_spec h i.val (Nat.zero_le _) (by have := i.isLt; omega)
  simp only [Nat.beq_eq] at h1
  have h1' : cd p y i.val = (α * cd p a i.val + β * cd p b i.val) % p := h1
  have h2 : (cd p y i.val : ZMod p) = ((α * cd p a i.val + β * cd p b i.val : ℕ) : ZMod p) := by
    apply natCast_eq_of_mod
    rw [Nat.mod_eq_of_lt (cd_lt hp.out.pos _ _)]
    exact h1'
  push_cast at h2
  simp only [vec_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact h2

/-! ## Normalised lists -/

/-- The first nonzero value of `f` on `i, i+1, …, i+k-1` is `1`. -/
def firstOne (f : ℕ → ℕ) : ℕ → ℕ → Bool
  | _, 0 => false
  | i, k + 1 => cond (Nat.beq (f i) 0) (firstOne f (i + 1) k) (Nat.beq (f i) 1)

theorem firstOne_spec (f : ℕ → ℕ) : ∀ k i, firstOne f i k = true →
    ∃ j, i ≤ j ∧ j < i + k ∧ f j = 1 ∧ ∀ j', i ≤ j' → j' < j → f j' = 0 := by
  intro k
  induction k with
  | zero => intro i h; simp [firstOne] at h
  | succ k ih =>
    intro i h
    simp only [firstOne] at h
    by_cases h0 : f i = 0
    · rw [show Nat.beq (f i) 0 = true by simpa using h0] at h
      obtain ⟨j, hj1, hj2, hj3, hj4⟩ := ih (i + 1) h
      refine ⟨j, by omega, by omega, hj3, fun j' h1 h2 => ?_⟩
      rcases Nat.eq_or_lt_of_le h1 with h | h
      · rw [← h]; exact h0
      · exact hj4 j' (by omega) h2
    · have hb : Nat.beq (f i) 0 = false := by
        rw [Bool.eq_false_iff]; intro hh; exact h0 (Nat.eq_of_beq_eq_true hh)
      rw [hb] at h
      simp only [Bool.cond_false, Nat.beq_eq] at h
      exact ⟨i, le_refl _, by omega, h, fun j' h1 h2 => by omega⟩

/-- A vector over `K` (indexed by `Fin n`) whose first nonzero coordinate is `1`. -/
def Nrm {K : Type*} [Zero K] [One K] {n : ℕ} (v : Fin n → K) : Prop :=
  ∃ k : Fin n, v k = 1 ∧ ∀ j : Fin n, j < k → v j = 0

theorem Nrm.ne_zero {K : Type*} [MonoidWithZero K] [Nontrivial K] {n : ℕ} {v : Fin n → K} (h : Nrm v) :
    v ≠ 0 := by
  obtain ⟨k, hk, -⟩ := h
  intro h0
  rw [h0] at hk
  exact zero_ne_one hk

/-- A normalised multiple of a normalised vector is the vector. -/
theorem Nrm.eq_of_smul {K : Type*} [Semiring K] [Nontrivial K] {n : ℕ} {v w : Fin n → K} (hv : Nrm v)
    (hw : Nrm w) {a : K} (h : w = a • v) : w = v := by
  obtain ⟨k, hk1, hk0⟩ := hv
  obtain ⟨k', hk1', hk0'⟩ := hw
  have hwk : ∀ j, w j = a * v j := fun j => by rw [h]; rfl
  rcases lt_trichotomy k' k with hlt | heq | hgt
  · have := hwk k'
    rw [hk0 k' hlt, mul_zero, hk1'] at this
    exact absurd this one_ne_zero
  · subst heq
    have ha : a = 1 := by have := hwk k'; rwa [hk1, mul_one, hk1', eq_comm] at this
    rw [h, ha, one_smul]
  · have := hwk k
    rw [hk0' k hgt, hk1, mul_one] at this
    have h0 : w = 0 := by rw [h, ← this, zero_smul]
    rw [h0] at hk1'
    exact absurd hk1' zero_ne_one

theorem nrm_vec {c : ℕ} (h : firstOne (cd p c) 0 7 = true) : Nrm (vec p c) := by
  obtain ⟨j, -, hj, h1, h0⟩ := firstOne_spec _ 7 0 h
  refine ⟨⟨j, by omega⟩, ?_, fun j' hj' => ?_⟩
  · simp only [vec_apply]; rw [h1]; simp
  · simp only [vec_apply]
    rw [h0 j'.val (Nat.zero_le _) hj']; simp

/-! ## Plücker coordinates -/

/-- The 21 index pairs `i < j`, in order. -/
def pairs : List (Fin 7 × Fin 7) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 3), (2, 4),
    (2, 5), (2, 6), (3, 4), (3, 5), (3, 6), (4, 5), (4, 6), (5, 6)]

theorem pairs_length : pairs.length = 21 := rfl

/-- `x_i y_j - x_j y_i` mod `p`, as a number below `p`. -/
def plN (p a b i j : ℕ) : ℕ :=
  Nat.mod (Nat.sub (Nat.add (Nat.mul (cd p a i) (cd p b j)) (Nat.mul p p)) (Nat.mul (cd p a j) (cd p b i))) p

theorem plN_lt (a b i j : ℕ) : plN p a b i j < p := Nat.mod_lt _ hp.out.pos

theorem plN_cast (a b : ℕ) (i j : Fin 7) :
    ((plN p a b i.val j.val : ℕ) : ZMod p) = pl (vec p a) (vec p b) i j := by
  have hle : cd p a j.val * cd p b i.val ≤ cd p a i.val * cd p b j.val + p * p := by
    have h1 := cd_lt hp.out.pos a j.val; have h2 := cd_lt hp.out.pos b i.val
    have : cd p a j.val * cd p b i.val ≤ p * p := Nat.mul_le_mul h1.le h2.le
    omega
  simp only [plN, pl, vec_apply]
  change (((cd p a i.val * cd p b j.val + p * p - cd p a j.val * cd p b i.val) % p : ℕ) : ZMod p) = _
  rw [ZMod.natCast_mod, Nat.cast_sub hle]
  push_cast
  rw [ZMod.natCast_self]
  ring

/-- The Plücker coordinates of the pair `(a, b)`. -/
def plL (p a b : ℕ) : List ℕ := pairs.map (fun ij => plN p a b ij.1.val ij.2.val)

/-- Their base-`p` number (the code of a line). -/
def plCode (p a b : ℕ) : ℕ := (plL p a b).foldr (fun t acc => Nat.add t (Nat.mul p acc)) 0

/-- The first nonzero entry of a list is `1`. -/
def firstOneL : List ℕ → Bool
  | [] => false
  | x :: l => cond (Nat.beq x 0) (firstOneL l) (Nat.beq x 1)

/-- The Plücker coordinates over `ZMod p`, as a function on `Fin 21`. -/
def plV {K : Type*} [Field K] (x y : V7 K) : Fin 21 → K :=
  fun k => pl x y (pairs.get ⟨k.val, by rw [pairs_length]; exact k.isLt⟩).1
    (pairs.get ⟨k.val, by rw [pairs_length]; exact k.isLt⟩).2

theorem plL_get (a b : ℕ) (k : Fin 21) :
    ((plL p a b).get ⟨k.val, by simp [plL, pairs_length]⟩ : ZMod p) = plV (vec p a) (vec p b) k := by
  simp only [plL, List.get_eq_getElem, List.getElem_map, plV]
  exact plN_cast a b _ _

theorem firstOneL_spec : ∀ l : List ℕ, firstOneL l = true →
    ∃ k < l.length, l[k]! = 1 ∧ ∀ j < k, l[j]! = 0 := by
  intro l
  induction l with
  | nil => intro h; simp [firstOneL] at h
  | cons x l ih =>
    intro h
    simp only [firstOneL] at h
    by_cases h0 : x = 0
    · rw [show Nat.beq x 0 = true by simpa using h0] at h
      obtain ⟨k, hk, h1, h2⟩ := ih h
      refine ⟨k + 1, by simp; omega, by simpa using h1, fun j hj => ?_⟩
      rcases j with _ | j
      · simpa using h0
      · simpa using h2 j (by omega)
    · have hb : Nat.beq x 0 = false := by
        rw [Bool.eq_false_iff]; intro hh; exact h0 (Nat.eq_of_beq_eq_true hh)
      rw [hb] at h
      simp only [Bool.cond_false, Nat.beq_eq] at h
      exact ⟨0, by simp, by simpa using h, fun j hj => by omega⟩

theorem nrm_plV {a b : ℕ} (h : firstOneL (plL p a b) = true) : Nrm (plV (vec p a) (vec p b)) := by
  obtain ⟨k, hk, h1, h0⟩ := firstOneL_spec _ h
  have hlen : (plL p a b).length = 21 := by simp [plL, pairs_length]
  refine ⟨⟨k, by omega⟩, ?_, fun j hj => ?_⟩
  · rw [← plL_get]
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)] at h1
    simp only [List.get_eq_getElem, Option.getD_some] at h1 ⊢
    rw [h1]; simp
  · rw [← plL_get]
    have hj' : j.val < k := hj
    have := h0 j.val hj'
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)] at this
    simp only [List.get_eq_getElem, Option.getD_some] at this ⊢
    rw [this]; simp

/-- Plücker coordinates of a change of basis. -/
theorem plV_comb {K : Type*} [Field K] (x y : V7 K) (s t u w : K) :
    plV (s • x + t • y) (u • x + w • y) = (s * w - t * u) • plV x y := by
  funext k
  simp only [plV, pl, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Equal Plücker lists from equal normalised Plücker vectors. -/
theorem plL_eq_of_plV {a b a' b' : ℕ} (h : plV (vec p a) (vec p b) = plV (vec p a') (vec p b')) :
    plL p a b = plL p a' b' := by
  have hlen : ∀ a b, (plL p a b).length = 21 := fun a b => by simp [plL, pairs_length]
  apply List.ext_get (by rw [hlen, hlen])
  intro k hk hk'
  have hk21 : k < 21 := by rw [hlen] at hk; exact hk
  have e1 := plL_get (p := p) a b ⟨k, hk21⟩
  have e2 := plL_get (p := p) a' b' ⟨k, hk21⟩
  rw [h, ← e2] at e1
  have := (ZMod.natCast_eq_natCast_iff' _ _ p).1 e1
  have l1 : (plL p a b).get ⟨k, hk⟩ < p := by simp [plL, plN_lt]
  have l2 : (plL p a' b').get ⟨k, hk'⟩ < p := by simp [plL, plN_lt]
  rwa [Nat.mod_eq_of_lt l1, Nat.mod_eq_of_lt l2] at this

end BipartiteDD.LeanAll.HexArith
