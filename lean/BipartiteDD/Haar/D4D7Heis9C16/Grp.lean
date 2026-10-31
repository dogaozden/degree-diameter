import Mathlib.Algebra.Group.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-! The group `G = Heis(F_9) ⋊ C_16` of order 432 (`SmallGroup(432,233)`), the group of the (4,7) Haar record on
864 vertices.

`F_9 = F_3[i]/(i² + 1)`, and `Heis(F_9)` is the set of pairs `(v, z)`, `v ∈ F_9`, `z ∈ F_3`, with
`(v, z)(w, z') = (v + w, z + z' + 2 ω(v, w))`, where `ω(v, w) = a b' − b a'` for `v = a + b i`, `w = a' + b' i`.
The generator `y` of `C_16` acts by `φ(v, z) = ((1 + i) v, −z)`. An element is `(a, b, z, j)` for `(a + b i, z, j)`,
with product `(v, z, j)(w, z', l) = ((v, z) φ^j(w, z'), j + l)`. Here `φ^j(w, z') = (μ^j w, (−1)^j z')` for
`μ = 1 + i`, and `μ^8 = 1`, so `μ^j` and `(−1)^j` only depend on `j` modulo 16.

The numbering `G ≃ Fin 432` is `(a, b, z, j) ↦ ((a·3 + b)·3 + z)·16 + j`, the same as the builder
`research/theorems/smallfam/graphs/build_d4D7_n864.py`. -/

namespace BipartiteDD.Haar.D4D7Heis9C16

/-- `μ^k = p + q i` for `μ = 1 + i`, as the pair `(p, q)`. Since `(p + q i)(1 + i) = (p − q) + (p + q) i`. -/
def mu : ℕ → ZMod 3 × ZMod 3
  | 0 => (1, 0)
  | k + 1 => ((mu k).1 - (mu k).2, (mu k).1 + (mu k).2)

/-- The real part of `μ^j`, for `j : ZMod 16`. -/
def P (j : ZMod 16) : ZMod 3 := (mu j.val).1

/-- The imaginary part of `μ^j`, for `j : ZMod 16`. -/
def Q (j : ZMod 16) : ZMod 3 := (mu j.val).2

/-- The sign `(−1)^j` by which `φ^j` acts on the centre `F_3`. -/
def S (j : ZMod 16) : ZMod 3 := (-1) ^ j.val

theorem P_zero : P 0 = 1 := by decide

theorem Q_zero : Q 0 = 0 := by decide

theorem S_zero : S 0 = 1 := by decide

theorem P_add (j l : ZMod 16) : P (j + l) = P j * P l - Q j * Q l := by
  revert j l
  decide +kernel

theorem Q_add (j l : ZMod 16) : Q (j + l) = P j * Q l + Q j * P l := by
  revert j l
  decide +kernel

theorem S_add (j l : ZMod 16) : S (j + l) = S j * S l := by
  revert j l
  decide +kernel

/-- `N(μ^j) = (−1)^j`: the norm of `1 + i` is `2 = −1` in `F_3`. -/
theorem S_eq_norm (j : ZMod 16) : S j = P j ^ 2 + Q j ^ 2 := by
  revert j
  decide +kernel

theorem S_neg (j : ZMod 16) : S (-j) = S j := by
  revert j
  decide +kernel

/-- Elements `(a + b i, z, j)` of `G`. -/
@[ext] structure Grp where
  a : ZMod 3
  b : ZMod 3
  z : ZMod 3
  j : ZMod 16
  deriving DecidableEq

/-- `(v, z, j)(w, z', l) = ((v, z) φ^j(w, z'), j + l)`, with `(v, z)(w, z') = (v + w, z + z' + 2 ω(v, w))`. -/
def mulG (x y : Grp) : Grp :=
  ⟨x.a + (P x.j * y.a - Q x.j * y.b), x.b + (P x.j * y.b + Q x.j * y.a),
    x.z + S x.j * y.z + 2 * (x.a * (P x.j * y.b + Q x.j * y.a) - x.b * (P x.j * y.a - Q x.j * y.b)), x.j + y.j⟩

/-- `(v, z, j)⁻¹ = (μ^{−j}(−v), −(−1)^j z, −j)`. -/
def invG (x : Grp) : Grp :=
  ⟨-(P (-x.j) * x.a - Q (-x.j) * x.b), -(P (-x.j) * x.b + Q (-x.j) * x.a), -(S x.j * x.z), -x.j⟩

theorem mulG_assoc (x y w : Grp) : mulG (mulG x y) w = mulG x (mulG y w) := by
  ext <;> simp only [mulG, P_add, Q_add, S_eq_norm] <;> ring

theorem mulG_one (x : Grp) : mulG ⟨0, 0, 0, 0⟩ x = x := by
  ext <;> simp [mulG, P_zero, Q_zero, S_zero]

theorem mulG_one' (x : Grp) : mulG x ⟨0, 0, 0, 0⟩ = x := by
  ext <;> simp [mulG]

theorem invG_mul (x : Grp) : mulG (invG x) x = ⟨0, 0, 0, 0⟩ := by
  ext <;> simp only [mulG, invG, S_neg] <;> ring

instance : Group Grp where
  mul := mulG
  one := ⟨0, 0, 0, 0⟩
  inv := invG
  mul_assoc := mulG_assoc
  one_mul := mulG_one
  mul_one := mulG_one'
  inv_mul_cancel := invG_mul

/-- The index `((a·3 + b)·3 + z)·16 + j` of `(a, b, z, j)`, a number in `0 … 431`. -/
def enc (g : Grp) : ℕ := ((g.a.val * 3 + g.b.val) * 3 + g.z.val) * 16 + g.j.val

theorem enc_lt (g : Grp) : enc g < 432 := by
  have h1 := ZMod.val_lt g.a
  have h2 := ZMod.val_lt g.b
  have h3 := ZMod.val_lt g.z
  have h4 := ZMod.val_lt g.j
  unfold enc
  omega

/-- The element with index `n`. -/
def grpOf (n : ℕ) : Grp :=
  ⟨((n / 144 : ℕ) : ZMod 3), ((n / 16 / 3 % 3 : ℕ) : ZMod 3), ((n / 16 % 3 : ℕ) : ZMod 3), ((n % 16 : ℕ) : ZMod 16)⟩

theorem grpOf_enc (g : Grp) : grpOf (enc g) = g := by
  obtain ⟨a, b, z, j⟩ := g
  revert a b z j
  decide +kernel

theorem enc_grpOf : ∀ n : Fin 432, enc (grpOf n.val) = n.val := by
  decide +kernel

/-- The numbering of `G` by `Fin 432`. -/
def equiv432 : Grp ≃ Fin 432 where
  toFun g := ⟨enc g, enc_lt g⟩
  invFun n := grpOf n.val
  left_inv g := grpOf_enc g
  right_inv n := Fin.ext (enc_grpOf n)

/-- The connection set `S` of the builder `build_d4D7_n864.py`, as `(a, b, z, j)`. -/
def s0 : Grp := ⟨0, 0, 0, 0⟩

def s1 : Grp := ⟨0, 2, 0, 9⟩

def s2 : Grp := ⟨2, 1, 0, 8⟩

def s3 : Grp := ⟨1, 2, 2, 14⟩

end BipartiteDD.Haar.D4D7Heis9C16
