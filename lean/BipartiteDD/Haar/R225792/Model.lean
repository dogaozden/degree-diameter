import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! The group `G = PSL(2,7) × SL(2,7) × Z/2` of the record Δ8·D8 with 225,792 vertices (job d8D8).

`SL(2,7)` is the group of `2×2` matrices over `ZMod 7` with determinant `1`. `PSL(2,7)` is `SL(2,7)` modulo
`±1`, realised by the canonical representative of each class: the matrix `X` with `key X ≤ key (-X)`, where
`key` reads the four entries as base-7 digits. The product of two classes is `canon (X * Y)`. Everything is
computable, so the facts about the enumerations are checked by `decide`. -/

namespace BipartiteDD.Haar.R225792

/-- A `2×2` matrix `[[a, b], [c, d]]` over `ZMod 7`. -/
structure M2 where
  a : ZMod 7
  b : ZMod 7
  c : ZMod 7
  d : ZMod 7
  deriving DecidableEq

instance : Inhabited M2 := ⟨⟨0, 0, 0, 0⟩⟩

namespace M2

/-- The matrix product. -/
def mul (x y : M2) : M2 :=
  ⟨x.a * y.a + x.b * y.c, x.a * y.b + x.b * y.d, x.c * y.a + x.d * y.c, x.c * y.b + x.d * y.d⟩

def neg (x : M2) : M2 := ⟨-x.a, -x.b, -x.c, -x.d⟩

def det (x : M2) : ZMod 7 := x.a * x.d - x.b * x.c

/-- The adjugate, which is the inverse when `det x = 1`. -/
def adj (x : M2) : M2 := ⟨x.d, -x.b, -x.c, x.a⟩

/-- The four entries as base-7 digits. -/
def key (x : M2) : ℕ := ((x.a.val * 7 + x.b.val) * 7 + x.c.val) * 7 + x.d.val

/-- The representative of `{x, -x}` with the smaller key. -/
def canon (x : M2) : M2 := if key x ≤ key (neg x) then x else neg x

def one : M2 := ⟨1, 0, 0, 1⟩

theorem mul_assoc' (x y z : M2) : (x.mul y).mul z = x.mul (y.mul z) := by
  obtain ⟨a, b, c, d⟩ := x
  obtain ⟨a', b', c', d'⟩ := y
  obtain ⟨a'', b'', c'', d''⟩ := z
  simp only [mul, M2.mk.injEq]
  refine ⟨by ring, by ring, by ring, by ring⟩

theorem one_mul' (x : M2) : one.mul x = x := by
  obtain ⟨a, b, c, d⟩ := x
  simp only [one, mul, M2.mk.injEq]
  refine ⟨by ring, by ring, by ring, by ring⟩

theorem mul_one' (x : M2) : x.mul one = x := by
  obtain ⟨a, b, c, d⟩ := x
  simp only [one, mul, M2.mk.injEq]
  refine ⟨by ring, by ring, by ring, by ring⟩

theorem neg_mul' (x y : M2) : (neg x).mul y = neg (x.mul y) := by
  obtain ⟨a, b, c, d⟩ := x
  obtain ⟨a', b', c', d'⟩ := y
  simp only [mul, neg, M2.mk.injEq]
  refine ⟨by ring, by ring, by ring, by ring⟩

theorem mul_neg' (x y : M2) : x.mul (neg y) = neg (x.mul y) := by
  obtain ⟨a, b, c, d⟩ := x
  obtain ⟨a', b', c', d'⟩ := y
  simp only [mul, neg, M2.mk.injEq]
  refine ⟨by ring, by ring, by ring, by ring⟩

theorem neg_neg' (x : M2) : neg (neg x) = x := by
  obtain ⟨a, b, c, d⟩ := x
  simp [neg]

theorem det_neg' (x : M2) : det (neg x) = det x := by
  obtain ⟨a, b, c, d⟩ := x
  simp only [det, neg]
  ring

theorem det_mul' (x y : M2) : det (x.mul y) = det x * det y := by
  obtain ⟨a, b, c, d⟩ := x
  obtain ⟨a', b', c', d'⟩ := y
  simp only [det, mul]
  ring

theorem det_adj' (x : M2) : det (adj x) = det x := by
  obtain ⟨a, b, c, d⟩ := x
  simp only [det, adj]
  ring

theorem adj_mul' (x : M2) (hx : det x = 1) : (adj x).mul x = one := by
  obtain ⟨a, b, c, d⟩ := x
  simp only [det, adj, mul, one, M2.mk.injEq] at hx ⊢
  refine ⟨by linear_combination hx, by ring, by ring, by linear_combination hx⟩

/-- Equal keys give equal matrices. -/
theorem key_inj {x y : M2} (h : key x = key y) : x = y := by
  obtain ⟨a, b, c, d⟩ := x
  obtain ⟨a', b', c', d'⟩ := y
  have ha := ZMod.val_lt a
  have hb := ZMod.val_lt b
  have hc := ZMod.val_lt c
  have hd := ZMod.val_lt d
  have ha' := ZMod.val_lt a'
  have hb' := ZMod.val_lt b'
  have hc' := ZMod.val_lt c'
  have hd' := ZMod.val_lt d'
  simp only [key] at h
  have h1 : a.val = a'.val := by omega
  have h2 : b.val = b'.val := by omega
  have h3 : c.val = c'.val := by omega
  have h4 : d.val = d'.val := by omega
  simp only [M2.mk.injEq]
  exact ⟨ZMod.val_injective 7 h1, ZMod.val_injective 7 h2, ZMod.val_injective 7 h3, ZMod.val_injective 7 h4⟩

theorem canon_mem (x : M2) : canon x = x ∨ canon x = neg x := by
  unfold canon
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem canon_neg' (x : M2) : canon (neg x) = canon x := by
  unfold canon
  rw [neg_neg']
  split_ifs with h1 h2 <;> first | rfl | exact key_inj (le_antisymm h1 h2) | (exfalso; omega)

theorem canon_canon (x : M2) : canon (canon x) = canon x := by
  rcases canon_mem x with h | h
  · rw [h, h]
  · rw [h, canon_neg', h]

theorem canon_mul_left' (x y : M2) : canon ((canon x).mul y) = canon (x.mul y) := by
  rcases canon_mem x with h | h
  · rw [h]
  · rw [h, neg_mul', canon_neg']

theorem canon_mul_right' (x y : M2) : canon (x.mul (canon y)) = canon (x.mul y) := by
  rcases canon_mem y with h | h
  · rw [h]
  · rw [h, mul_neg', canon_neg']

theorem det_canon' (x : M2) : det (canon x) = det x := by
  rcases canon_mem x with h | h
  · rw [h]
  · rw [h, det_neg']

theorem canon_one : canon one = one := by decide +kernel

end M2

/-- `PSL(2,7)`: the canonical representatives of the classes of `SL(2,7)` modulo `±1`. -/
def PSL : Type := {x : M2 // x.det = 1 ∧ M2.canon x = x}

instance : DecidableEq PSL :=
  inferInstanceAs (DecidableEq {x : M2 // x.det = 1 ∧ M2.canon x = x})

theorem canon_mem_psl (z : M2) (hz : z.det = 1) :
    (M2.canon z).det = 1 ∧ M2.canon (M2.canon z) = M2.canon z :=
  ⟨by rw [M2.det_canon', hz], M2.canon_canon z⟩

instance : Mul PSL :=
  ⟨fun x y => ⟨M2.canon (x.1.mul y.1), canon_mem_psl _ (by rw [M2.det_mul', x.2.1, y.2.1, one_mul])⟩⟩

instance : One PSL := ⟨⟨M2.one, by decide +kernel, M2.canon_one⟩⟩

instance : Inv PSL :=
  ⟨fun x => ⟨M2.canon (M2.adj x.1), canon_mem_psl _ (by rw [M2.det_adj', x.2.1])⟩⟩

instance : Group PSL where
  mul_assoc x y z := Subtype.ext (by
    show M2.canon ((M2.canon (x.1.mul y.1)).mul z.1) = M2.canon (x.1.mul (M2.canon (y.1.mul z.1)))
    rw [M2.canon_mul_left', M2.canon_mul_right', M2.mul_assoc'])
  one_mul x := Subtype.ext (by
    show M2.canon (M2.one.mul x.1) = x.1
    rw [M2.one_mul']
    exact x.2.2)
  mul_one x := Subtype.ext (by
    show M2.canon (x.1.mul M2.one) = x.1
    rw [M2.mul_one']
    exact x.2.2)
  inv_mul_cancel x := Subtype.ext (by
    show M2.canon ((M2.canon (M2.adj x.1)).mul x.1) = M2.one
    rw [M2.canon_mul_left', M2.adj_mul' x.1 x.2.1]
    exact M2.canon_one)

/-- `SL(2,7)`: the matrices of determinant `1`. -/
def SL : Type := {x : M2 // x.det = 1}

instance : DecidableEq SL :=
  inferInstanceAs (DecidableEq {x : M2 // x.det = 1})

instance : Mul SL := ⟨fun x y => ⟨x.1.mul y.1, by rw [M2.det_mul', x.2, y.2, one_mul]⟩⟩

instance : One SL := ⟨⟨M2.one, by decide +kernel⟩⟩

instance : Inv SL := ⟨fun x => ⟨M2.adj x.1, by rw [M2.det_adj', x.2]⟩⟩

instance : Group SL where
  mul_assoc x y z := Subtype.ext (M2.mul_assoc' _ _ _)
  one_mul x := Subtype.ext (M2.one_mul' _)
  mul_one x := Subtype.ext (M2.mul_one' _)
  inv_mul_cancel x := Subtype.ext (M2.adj_mul' _ x.2)

/-- The group of the record: `PSL(2,7) × SL(2,7) × Z/2`, of order `168 · 336 · 2 = 112896`. -/
abbrev G8 := PSL × SL × Multiplicative (ZMod 2)

end BipartiteDD.Haar.R225792
