#!/usr/bin/env python3
"""Covering certificates for the (6,10) record on 524,160 vertices: G = SL(2,5) x PSL(2,7) x Z_13 (order 262080),
S from research/frontier/sols/d6D10_prod_sl_5_psl_7_13_orb3f0_s1.txt.

Cover (one nine-letter condition, lean/BipartiteDD/Haar/Diam10.lean): every g in G is
  x1 x2^-1 x3 x4^-1 x5 x6^-1 x7 x8^-1 x9      with all xi in S.
Letter k of the code c = sum d_k 6^k is s_{d_k} of S, inverted when k is odd.

Numbering (must match lean/BipartiteDD/Haar/D6D10d/SL5.lean, PSL7.lean, Base.lean):
  SL(2,5) class (a,b,c,d): n = (a-1)*5 + b if c = 0, else 20 + ((c-1)*5 + a)*5 + d.
  PSL(2,7) class: its representative with posP(a,c) (a <= 3 if c = 0, else c <= 3); numbered
    n = (a-1)*7 + b if c = 0, else 21 + ((c-1)*7 + a)*7 + d.
  Element (X, Y, z) of G has index (encS(X) * 168 + encP(Y)) * 13 + z.

Usage: python3 gen_d6D10d.py SOL.txt LEANDIR
Writes LEANDIR/{Gens,Check,Base,Words,Cover}.lean, LEANDIR/Stage00..47.lean, and LEANDIR/SL5.lean, PSL7.lean
(templated from lean/BipartiteDD/Haar/SL19.lean and D7D8/PSL19.lean). Every index is re-checked exactly in Python
before anything is written. Build the Lean modules one at a time (lake build BipartiteDD.Haar.D6D10d.<Module>).
"""
import os
import re
import sys

import numpy as np

P5, P7, NZ = 5, 7, 13
NSL, NPSL = 120, 168
N = NSL * NPSL * NZ  # 262080
NS = 6
DIG = 9
STAGE = 5460  # 262080 = 48 * 5460
NSTAGES = N // STAGE
assert NSTAGES * STAGE == N
BITS = 24  # codes < 6^9 < 2^24
HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", ".."))
SRC_SL19 = os.path.join(REPO, "lean", "BipartiteDD", "Haar", "SL19.lean")
SRC_PSL19 = os.path.join(REPO, "lean", "BipartiteDD", "Haar", "D7D8", "PSL19.lean")


def parse_sol(path):
    lines = [ln.strip() for ln in open(path) if ln.strip()]
    head = lines[0].split()
    assert head[2:5] == ["prod", "sl", "5"] and head[5:7] == ["psl", "7"] and head[8] == "13", head
    assert int(head[-1]) == N, head
    S = []
    for ln in lines[1:]:
        m = re.fullmatch(r"\d+\s+prod\[mat\((\d+),(\d+),(\d+),(\d+)\);mat\((\d+),(\d+),(\d+),(\d+)\)\] z=(\d+)", ln)
        assert m, ln
        v = list(map(int, m.groups()))
        X = tuple(t % P5 for t in v[0:4])
        Y = tuple(t % P7 for t in v[4:8])
        assert (X[0] * X[3] - X[1] * X[2]) % P5 == 1, ln  # SL(2,5)
        assert (Y[0] * Y[3] - Y[1] * Y[2]) % P7 == 1, ln  # PSL(2,7) representative, det 1
        S.append((X, Y, v[8] % NZ))
    assert len(S) == NS and len(set(S)) == NS, S
    return S


# ---- exact Python mirrors of the Lean normal forms ------------------------------------------------------------

def mul(x, y, p):
    a, b, c, d = x
    e, f, g, h = y
    return ((a * e + b * g) % p, (a * f + b * h) % p, (c * e + d * g) % p, (c * f + d * h) % p)


def adj(x, p):
    a, b, c, d = x
    return (d % p, (-b) % p, (-c) % p, a % p)


def canon7(x):
    a, b, c, d = x
    pos = (a <= 3) if c == 0 else (c <= 3)
    return (a, b, c, d) if pos else tuple((-t) % P7 for t in x)


def encS(x):
    a, b, c, d = x
    return (a - 1) * 5 + b if c == 0 else 20 + ((c - 1) * 5 + a) * 5 + d


def encP(x):
    a, b, c, d = x
    return (a - 1) * 7 + b if c == 0 else 21 + ((c - 1) * 7 + a) * 7 + d


def quadS(n):
    """Inverse of encS on the SL(2,5) normal forms (mirror of SL5.quad)."""
    inv5 = [0, 1, 3, 2, 4]
    if n < 20:
        a = n // 5 + 1
        return (a, n % 5, 0, inv5[a])
    m = n - 20
    c, a, d = m // 25 + 1, m // 5 % 5, m % 5
    return (a, (a * d - 1) * inv5[c] % 5, c, d)


def quadP(n):
    """Inverse of encP on the PSL(2,7) normal forms (mirror of PSL7.quad)."""
    inv7 = [0, 1, 4, 5, 2, 3, 6]
    if n < 21:
        a = n // 7 + 1
        return (a, n % 7, 0, inv7[a])
    m = n - 21
    c, a, d = m // 49 + 1, m // 7 % 7, m % 7
    return (a, (a * d - 1) * inv7[c] % 7, c, d)


def word_exact(digs, S):
    """The nine-letter word of the digits, as (SL part, canonical PSL part, z) — exact Python."""
    X, Y, z = (1, 0, 0, 1), (1, 0, 0, 1), 0
    for k, d in enumerate(digs):
        xs, ys, zs = S[d]
        if k % 2 == 0:
            X = mul(X, xs, P5)
            Y = mul(Y, ys, P7)
            z += zs
        else:
            X = mul(X, adj(xs, P5), P5)
            Y = mul(Y, adj(ys, P7), P7)
            z -= zs
    return X, canon7(Y), z % NZ


def index_of(X, Y, z):
    return (encS(X) * NPSL + encP(Y)) * NZ + z


def find_codes(S):
    """First code (smallest integer) for every index, by vectorised search over all 6^9 codes."""
    ncode = NS ** DIG
    codes = np.arange(ncode, dtype=np.int64)
    # letter tables per position k: entries for digit j
    sl_tab = []
    ps_tab = []
    z_tab = []
    for k in range(DIG):
        sl_rows = [[], [], [], []]
        ps_rows = [[], [], [], []]
        zr = []
        for j in range(NS):
            xs, ys, zs = S[j]
            if k % 2 == 0:
                xa, ya, za = xs, ys, zs
            else:
                xa, ya, za = adj(xs, P5), adj(ys, P7), (-zs) % NZ
            for t in range(4):
                sl_rows[t].append(xa[t])
                ps_rows[t].append(ya[t])
            zr.append(za)
        sl_tab.append([np.array(r, dtype=np.int64) for r in sl_rows])
        ps_tab.append([np.array(r, dtype=np.int64) for r in ps_rows])
        z_tab.append(np.array(zr, dtype=np.int64))
    dig = [(codes // NS ** k) % NS for k in range(DIG)]
    # SL(2,5) product, then PSL(2,7) product of representatives (sign fixed at the end), then the Z_13 sum
    M = [np.ones(ncode, dtype=np.int64), np.zeros(ncode, dtype=np.int64),
         np.zeros(ncode, dtype=np.int64), np.ones(ncode, dtype=np.int64)]
    Q = [np.ones(ncode, dtype=np.int64), np.zeros(ncode, dtype=np.int64),
         np.zeros(ncode, dtype=np.int64), np.ones(ncode, dtype=np.int64)]
    Z = np.zeros(ncode, dtype=np.int64)
    for k in range(DIG):
        d = dig[k]
        L = [sl_tab[k][t][d] for t in range(4)]
        M = list(mul_vec(M, L, P5))
        R = [ps_tab[k][t][d] for t in range(4)]
        Q = list(mul_vec(Q, R, P7))
        Z = (Z + z_tab[k][d]) % NZ
    a, b, c, dd = Q
    pos = np.where(c == 0, a <= 3, c <= 3)
    Q = [np.where(pos, t, (-t) % P7) for t in Q]
    encs = np.where(M[2] == 0, (M[0] - 1) * 5 + M[1], 20 + ((M[2] - 1) * 5 + M[0]) * 5 + M[3])
    encp = np.where(Q[2] == 0, (Q[0] - 1) * 7 + Q[1], 21 + ((Q[2] - 1) * 7 + Q[0]) * 7 + Q[3])
    idx = (encs * NPSL + encp) * NZ + Z
    uniq, first = np.unique(idx, return_index=True)
    assert len(uniq) == N and uniq[0] == 0 and uniq[-1] == N - 1, (len(uniq), uniq[:3], uniq[-3:])
    out = np.empty(N, dtype=np.int64)
    out[uniq] = first  # first occurrence = smallest code, since codes are sorted
    return out


def mul_vec(x, y, p):
    a, b, c, d = x
    e, f, g, h = y
    return ((a * e + b * g) % p, (a * f + b * h) % p, (c * e + d * g) % p, (c * f + d * h) % p)


def verify(S, codes):
    """Exact check of every index: the word of the stored code is the element with that index."""
    for n in range(N):
        digs = [(int(codes[n]) // NS ** k) % NS for k in range(DIG)]
        X, Y, z = word_exact(digs, S)
        assert index_of(X, Y, z) == n, ("index", n, digs)
        # and the normal forms decode back to the element
        assert quadS(encS(X)) == X and quadP(encP(Y)) == Y, ("decode", n)


# ---- Lean modules --------------------------------------------------------------------------------------------

SL5_DOC = """/-! The group `SL(2, 5)` of order 120, with a computable numbering of its elements by `Fin 120`.

Elements are matrices `[[a, b], [c, d]]` over `ZMod 5` with `a * d - b * c = 1`, multiplied as matrices. The numbering
is `enc`: the 20 elements with `c = 0` come first (`n = (a - 1) * 5 + b`), then the 100 with `c ≠ 0`
(`n = 20 + ((c - 1) * 5 + a) * 5 + d`). `quad` inverts `enc` on the determinant-one matrices; `quad_enc` and `enc_quad`
check this on all of them by computation. Templated from `lean/BipartiteDD/Haar/SL19.lean` by
research/lean-haarD/gen_d6D10d.py. -/"""

PSL7_DOC = """/-! The group `PSL(2, 7)` of order 168, with a computable numbering by `ℕ`.

An element is a matrix `[[a, b], [c, d]]` over `ZMod 7` of determinant `1`, taken modulo `±1`. Each class has one
representative with `posB a c`: `a` when `c = 0`, and `c` otherwise, lies in `{0, …, 3}` in `ZMod 7`'s values. The
product is the matrix product, normalised by `canon`. The numbering is `enc`/`quad`: the `c = 0` elements come first
(`n = (a - 1) * 7 + b`, `a ∈ 1…3`), then the `c ≠ 0` ones (`n = 21 + ((c - 1) * 7 + a) * 7 + d`, `c ∈ 1…3`), with `b`
determined by the determinant. Templated from `lean/BipartiteDD/Haar/D7D8/PSL19.lean` by
research/lean-haarD/gen_d6D10d.py. -/"""


def template_sl5(src):
    s = src.replace("BipartiteDD.Haar.SL19", "BipartiteDD.Haar.D6D10d.SL5")
    s = re.sub(r"/-!.*?-/", SL5_DOC, s, count=1, flags=re.S)
    s = re.sub(r"def invTab : List \(ZMod 19\) :=\s*\[[^\]]*\]", "def invTab : List (ZMod 5) :=\n  [0, 1, 3, 2, 4]", s)
    s = s.replace("6840", "120").replace("342", "20").replace("6859", "125").replace("361", "25")
    s = s.replace("19", "5")
    s = s.replace("SL(2, 5)", "SL(2, 5)")
    assert "19" not in s and "6840" not in s, "leftover constant"
    return s


def template_psl7(src):
    s = src.replace("BipartiteDD.Haar.PSL19", "BipartiteDD.Haar.D6D10d.PSL7")
    s = re.sub(r"/-!.*?-/", PSL7_DOC, s, count=1, flags=re.S)
    s = re.sub(r"def invTab : List \(ZMod 19\) :=\s*\[[^\]]*\]", "def invTab : List (ZMod 7) :=\n  [0, 1, 4, 5, 2, 3, 6]", s)
    s = s.replace("3420", "168").replace("171", "21").replace("361", "49")
    s = s.replace("19", "7")
    s = re.sub(r"(?<![\w.])9(?!\d)", "3", s)
    assert "19" not in s and "3420" not in s, "leftover constant"
    return s


def gens_module(S):
    rows = []
    for xs, ys, z in S:
        sl = "⟨%d, %d, %d, %d, by decide⟩" % xs
        ps = "⟨%d, %d, %d, %d, by decide, by decide⟩" % canon7(ys)
        rows.append("⟨%s, %s, Multiplicative.ofAdd (%d : ZMod 13)⟩" % (sl, ps, z))
    body = ",\n    ".join(rows)
    return f"""import BipartiteDD.Haar.D6D10d.Base

/-! The six generators `S` of the Δ6·D10 record (`d6D10_prod_sl_5_psl_7_13_orb3f0_s1`), as elements of
`SL(2,5) × PSL(2,7) × ZMod 13` in the normal forms of `SL5` and `PSL7`. Generated by
research/lean-haarD/gen_d6D10d.py. Do not edit by hand. -/

namespace BipartiteDD.Haar.D6D10d

/-- The generators, indexed `0 … 5`; index `0` is the identity. -/
def sGl : List G :=
  [{body}]

end BipartiteDD.Haar.D6D10d
"""


BASE = """import BipartiteDD.Haar.D6D10d.SL5
import BipartiteDD.Haar.D6D10d.PSL7
import Mathlib.Logic.Equiv.Fin.Basic

/-! The group `G = SL(2, 5) × PSL(2, 7) × Z_13` of the Δ6·D10 record (order 262080), and its numbering by `Fin 262080`.

`G` is a structure with componentwise operations (not the `Prod` group), so that the projections of a product are
computed by the direct operations of `SL5.Grp`, `PSL7.Grp` and `Multiplicative (ZMod 13)`; this keeps the
defeq checks between the word and the Nat-level check cheap. The index of `x` is
`(SL5.enc x.s * 168 + PSL7.enc x.p) * 13 + x.z`. -/

namespace BipartiteDD.Haar.D6D10d

/-- The group `SL(2, 5) × PSL(2, 7) × Z_13`; the last factor is `Multiplicative (ZMod 13)`, so it adds. -/
@[ext]
structure G where
  s : SL5.Grp
  p : PSL7.Grp
  z : Multiplicative (ZMod 13)
  deriving DecidableEq

instance : Mul G := ⟨fun x y => ⟨x.s * y.s, x.p * y.p, x.z * y.z⟩⟩
instance : One G := ⟨⟨1, 1, 1⟩⟩
instance : Inv G := ⟨fun x => ⟨x.s⁻¹, x.p⁻¹, x.z⁻¹⟩⟩

theorem mul_s (x y : G) : (x * y).s = x.s * y.s := rfl
theorem mul_p (x y : G) : (x * y).p = x.p * y.p := rfl
theorem mul_z (x y : G) : (x * y).z = x.z * y.z := rfl
theorem one_s : (1 : G).s = 1 := rfl
theorem one_p : (1 : G).p = 1 := rfl
theorem one_z : (1 : G).z = 1 := rfl
theorem inv_s (x : G) : (x⁻¹).s = x.s⁻¹ := rfl
theorem inv_p (x : G) : (x⁻¹).p = x.p⁻¹ := rfl
theorem inv_z (x : G) : (x⁻¹).z = x.z⁻¹ := rfl

instance : Group G where
  mul_assoc x y z := by
    refine G.ext ?_ ?_ ?_ <;> simp only [mul_s, mul_p, mul_z, mul_assoc]
  one_mul x := by
    refine G.ext ?_ ?_ ?_ <;> simp only [mul_s, mul_p, mul_z, one_s, one_p, one_z, one_mul]
  mul_one x := by
    refine G.ext ?_ ?_ ?_ <;> simp only [mul_s, mul_p, mul_z, one_s, one_p, one_z, mul_one]
  inv_mul_cancel x := by
    refine G.ext ?_ ?_ ?_ <;>
      simp only [mul_s, mul_p, mul_z, inv_s, inv_p, inv_z, one_s, one_p, one_z, inv_mul_cancel]

/-- The index of `x`. -/
def idxG (x : G) : ℕ :=
  (SL5.enc x.s.a x.s.b x.s.c x.s.d * 168 + PSL7.enc x.p.a x.p.b x.p.c x.p.d) * 13
    + (Multiplicative.toAdd x.z).val

/-- The element with index `n`. -/
def gOf (n : ℕ) : G :=
  ⟨SL5.grpOf (n / 13 / 168), PSL7.grpP (n / 13 % 168), Multiplicative.ofAdd ((n % 13 : ℕ) : ZMod 13)⟩

theorem idxG_lt (x : G) : idxG x < 262080 := by
  have h1 := SL5.enc_lt x.s
  have h2 := PSL7.enc_lt x.p
  have h3 := ZMod.val_lt (Multiplicative.toAdd x.z)
  unfold idxG
  omega

theorem gOf_idxG (x : G) : gOf (idxG x) = x := by
  have h1 := SL5.enc_lt x.s
  have h2 := PSL7.enc_lt x.p
  have h3 := ZMod.val_lt (Multiplicative.toAdd x.z)
  have e1 : idxG x / 13 / 168 = SL5.enc x.s.a x.s.b x.s.c x.s.d := by
    unfold idxG
    omega
  have e2 : idxG x / 13 % 168 = PSL7.enc x.p.a x.p.b x.p.c x.p.d := by
    unfold idxG
    omega
  have e3 : idxG x % 13 = (Multiplicative.toAdd x.z).val := by
    unfold idxG
    omega
  unfold gOf
  rw [e1, e2, e3, SL5.grpOf_enc, PSL7.grpP_enc, ZMod.natCast_zmod_val]
  rfl

theorem idxG_gOf (n : ℕ) (hn : n < 262080) : idxG (gOf n) = n := by
  have hx : n / 13 / 168 < 120 := by omega
  have hy : n / 13 % 168 < 168 := Nat.mod_lt _ (by norm_num)
  have h1 : SL5.enc (SL5.grpOf (n / 13 / 168)).a (SL5.grpOf (n / 13 / 168)).b
      (SL5.grpOf (n / 13 / 168)).c (SL5.grpOf (n / 13 / 168)).d = n / 13 / 168 := by
    obtain ⟨ha, hb, hc, hd⟩ := SL5.grpOf_fields hx
    rw [ha, hb, hc, hd]
    exact SL5.enc_quad _ hx
  have h2 : PSL7.enc (PSL7.grpP (n / 13 % 168)).a (PSL7.grpP (n / 13 % 168)).b
      (PSL7.grpP (n / 13 % 168)).c (PSL7.grpP (n / 13 % 168)).d = n / 13 % 168 :=
    PSL7.enc_grpP _ hy
  have h3 : (Multiplicative.toAdd (Multiplicative.ofAdd ((n % 13 : ℕ) : ZMod 13))).val = n % 13 := by
    show (((n % 13 : ℕ) : ZMod 13)).val = n % 13
    rw [ZMod.val_natCast, Nat.mod_mod]
  unfold idxG gOf
  dsimp only
  rw [h1, h2, h3]
  omega

/-- The numbering of `G` by `Fin 262080`. -/
def equivG : G ≃ Fin 262080 where
  toFun x := ⟨idxG x, idxG_lt x⟩
  invFun n := gOf n.1
  left_inv x := gOf_idxG x
  right_inv n := Fin.ext (idxG_gOf n.1 n.2)

/-- `G ⊕ G ≃ Fin 524160`: the two sides of the Haar graph. -/
def haarVert : G ⊕ G ≃ Fin 524160 :=
  (Equiv.sumCongr equivG equivG).trans (finSumFinEquiv.trans (finCongr (by norm_num)))

end BipartiteDD.Haar.D6D10d
"""

WORDS = """import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Finset.Basic

/-! The nine-letter covering word of a group, and the covering hypothesis `CoverHyp` of `Diam10` written as a
definition, so that its unfolding matches the word term for term (see research/lean-haarD/STATUS-d6D10c.md). -/

namespace BipartiteDD.Haar.D6D10d

/-- The nine-letter alternating word `x₁ x₂⁻¹ x₃ x₄⁻¹ x₅ x₆⁻¹ x₇ x₈⁻¹ x₉` in a group, right-nested. -/
def wordOf {G : Type*} [Group G] (x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ : G) : G :=
  x₁ * (x₂⁻¹ * (x₃ * (x₄⁻¹ * (x₅ * (x₆⁻¹ * (x₇ * (x₈⁻¹ * x₉)))))))

/-- The covering hypothesis of `haar_isBipartiteDegDiam10_of_equiv`, for a general group. -/
def CoverHyp {G : Type*} [Group G] (S : Finset G) : Prop :=
  ∀ g : G, ∃ x₁ ∈ S, ∃ x₂ ∈ S, ∃ x₃ ∈ S, ∃ x₄ ∈ S, ∃ x₅ ∈ S, ∃ x₆ ∈ S, ∃ x₇ ∈ S, ∃ x₈ ∈ S,
    ∃ x₉ ∈ S, g = x₁ * (x₂⁻¹ * (x₃ * (x₄⁻¹ * (x₅ * (x₆⁻¹ * (x₇ * (x₈⁻¹ * x₉)))))))

end BipartiteDD.Haar.D6D10d
"""

CHECK = """import BipartiteDD.Haar.D6D10d.Gens
import BipartiteDD.Haar.D6D10d.Words

/-! The connection set `SS` of the Δ6·D10 record and the covering words `wordC c` (code `c` in base `6`, nine digits).
The stage tables are checked on Nat quadruples in `NatCheck`. Generated by research/lean-haarD/gen_d6D10d.py. -/

namespace BipartiteDD.Haar.D6D10d

/-- The `i`-th generator. -/
def sG (i : ℕ) : G := sGl.getD i 1

/-- The connection set. -/
def SS : Finset G := {sG 0, sG 1, sG 2, sG 3, sG 4, sG 5}

theorem card_SS : SS.card = 6 := by
  decide +kernel

theorem sG_mem (j : ℕ) (hj : j < 6) : sG j ∈ SS := by
  have h : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [SS]

/-- The digit `k` of the code `c`, in base `6`. -/
def dig (c k : ℕ) : ℕ := c / 6 ^ k % 6

theorem dig_lt (c k : ℕ) : dig c k < 6 := Nat.mod_lt _ (by norm_num)

/-- The covering word of the code `c`. -/
def wordC (c : ℕ) : G :=
  wordOf (sG (dig c 0)) (sG (dig c 1)) (sG (dig c 2)) (sG (dig c 3)) (sG (dig c 4)) (sG (dig c 5))
    (sG (dig c 6)) (sG (dig c 7)) (sG (dig c 8))

end BipartiteDD.Haar.D6D10d
"""



def nest_expr(L, m, adj):
    """The nested nine-letter product x1 (x2^-1 (x3 (... x9))) of the letter expressions L, in the shape of `wordOf`,
    with `m` the Nat multiplication and `adj` the inverse (applied at odd positions)."""
    e = L[8]
    for k in range(7, -1, -1):
        letter = "(%s %s)" % (adj, L[k]) if k % 2 == 1 else L[k]
        e = "(%s %s %s)" % (m, letter, e)
    return e


def prod_lean():
    sl = nest_expr(["(letS c %d)" % k for k in range(DIG)], "mulS", "adjS")
    ps = nest_expr(["(letP c %d)" % k for k in range(DIG)], "mulP", "adjP")
    return (
        "/-- The `SL(2,5)` letter of the code `c` at position `k`, as a Nat quadruple. -/\n"
        "def letS (c k : ℕ) : N4 := sTabS.getD (dig c k) (1, 0, 0, 1)\n\n"
        "/-- The `PSL(2,7)` letter of the code `c` at position `k`, as a Nat quadruple. -/\n"
        "def letP (c k : ℕ) : N4 := sTabP.getD (dig c k) (1, 0, 0, 1)\n\n"
        "/-- The `SL(2,5)` part of the nine-letter word of the code `c`, as a Nat quadruple. -/\n"
        "def prodS (c : ℕ) : N4 :=\n  " + sl + "\n\n"
        "/-- The `PSL(2,7)` part of the nine-letter word of the code `c`, as a Nat quadruple (up to sign). -/\n"
        "def prodP (c : ℕ) : N4 :=\n  " + ps + "\n\n")


NATCHECK = """import BipartiteDD.Haar.D6D10d.Check
import Mathlib.Tactic.IntervalCases

/-! The stage check of the Δ6·D10 covering condition, on `Nat` quadruples.

The `SL(2,5)` and `PSL(2,7)` parts of the nine-letter word of a code `c` (base `6`, nine digits) are products of
`Nat` quadruples, reduced mod `5` and `7`: `prodS c` and `prodP c`. The `Z_13` part is `zc c`. `okN c n` checks these
against the normal forms of the index `n` (`SL5.quad`, `PSL7.quad`, and `n % 13`), and `okN_spec` turns the check into
`gOf n = wordC c`. The `PSL(2,7)` relation is up to sign, since `PSL(2,7)` is a quotient. The tables are generated by
research/lean-haarD/gen_d6D10d.py; do not edit by hand. -/

namespace BipartiteDD.Haar.D6D10d

abbrev N4 := ℕ × ℕ × ℕ × ℕ
abbrev Q5 := ZMod 5 × ZMod 5 × ZMod 5 × ZMod 5
abbrev Q7 := ZMod 7 × ZMod 7 × ZMod 7 × ZMod 7

/-- The `SL(2,5)` parts of the generators `sG j`, as Nat quadruples. -/
def sTabS : List N4 := [@@SL@@]

/-- The `PSL(2,7)` parts of the generators, as Nat quadruples (their normal forms). -/
def sTabP : List N4 := [@@PS@@]

/-- The `Z_13` exponents of the generators. -/
def zTab : List ℕ := [@@Z@@]

def mulS (x y : N4) : N4 :=
  ((x.1 * y.1 + x.2.1 * y.2.2.1) % 5, (x.1 * y.2.1 + x.2.1 * y.2.2.2) % 5,
    (x.2.2.1 * y.1 + x.2.2.2 * y.2.2.1) % 5, (x.2.2.1 * y.2.1 + x.2.2.2 * y.2.2.2) % 5)

/-- The inverse in `SL(2,5)`: the adjugate, with `-b = 4 b` in `ZMod 5`. -/
def adjS (x : N4) : N4 := (x.2.2.2 % 5, (4 * x.2.1) % 5, (4 * x.2.2.1) % 5, x.1 % 5)

def mulP (x y : N4) : N4 :=
  ((x.1 * y.1 + x.2.1 * y.2.2.1) % 7, (x.1 * y.2.1 + x.2.1 * y.2.2.2) % 7,
    (x.2.2.1 * y.1 + x.2.2.2 * y.2.2.1) % 7, (x.2.2.1 * y.2.1 + x.2.2.2 * y.2.2.2) % 7)

/-- The adjugate in `PSL(2,7)`, up to sign: `-b = 6 b` in `ZMod 7`. -/
def adjP (x : N4) : N4 := (x.2.2.2 % 7, (6 * x.2.1) % 7, (6 * x.2.2.1) % 7, x.1 % 7)

def cS (x : N4) : Q5 := ((x.1 : ZMod 5), (x.2.1 : ZMod 5), (x.2.2.1 : ZMod 5), (x.2.2.2 : ZMod 5))

def cP (x : N4) : Q7 := ((x.1 : ZMod 7), (x.2.1 : ZMod 7), (x.2.2.1 : ZMod 7), (x.2.2.2 : ZMod 7))

def negQ7 (q : Q7) : Q7 := (-q.1, -q.2.1, -q.2.2.1, -q.2.2.2)

theorem four5 : (4 : ZMod 5) = -1 := by decide

theorem six7 : (6 : ZMod 7) = -1 := by decide

theorem twelve13 : (12 : ZMod 13) = -1 := by decide

/-- `g : SL(2,5)` has the matrix entries of `x`. -/
abbrev EqS (g : SL5.Grp) (x : N4) : Prop :=
  g.a = (x.1 : ZMod 5) ∧ g.b = (x.2.1 : ZMod 5) ∧ g.c = (x.2.2.1 : ZMod 5) ∧ g.d = (x.2.2.2 : ZMod 5)

/-- `g : PSL(2,7)` has the matrix entries of `x`, or their negatives. -/
abbrev EqP (g : PSL7.Grp) (x : N4) : Prop :=
  (g.a = (x.1 : ZMod 7) ∧ g.b = (x.2.1 : ZMod 7) ∧ g.c = (x.2.2.1 : ZMod 7) ∧ g.d = (x.2.2.2 : ZMod 7)) ∨
    (g.a = -(x.1 : ZMod 7) ∧ g.b = -(x.2.1 : ZMod 7) ∧ g.c = -(x.2.2.1 : ZMod 7) ∧ g.d = -(x.2.2.2 : ZMod 7))

theorem eqS_mul {g h : SL5.Grp} {x y : N4} (hg : EqS g x) (hh : EqS h y) : EqS (g * h) (mulS x y) := by
  obtain ⟨g1, g2, g3, g4⟩ := hg
  obtain ⟨h1, h2, h3, h4⟩ := hh
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [SL5.mul_a, g1, g2, h1, h3, mulS, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul]
  · simp only [SL5.mul_b, g1, g2, h2, h4, mulS, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul]
  · simp only [SL5.mul_c, g3, g4, h1, h3, mulS, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul]
  · simp only [SL5.mul_d, g3, g4, h2, h4, mulS, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul]

theorem eqS_inv {g : SL5.Grp} {x : N4} (hg : EqS g x) : EqS g⁻¹ (adjS x) := by
  obtain ⟨g1, g2, g3, g4⟩ := hg
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [SL5.inv_a, g4, adjS, ZMod.natCast_mod]
  · simp only [SL5.inv_b, g2, adjS, ZMod.natCast_mod, Nat.cast_mul, Nat.cast_ofNat, four5]
    ring
  · simp only [SL5.inv_c, g3, adjS, ZMod.natCast_mod, Nat.cast_mul, Nat.cast_ofNat, four5]
    ring
  · simp only [SL5.inv_d, g1, adjS, ZMod.natCast_mod]

theorem eqP_mul {g h : PSL7.Grp} {x y : N4} (hg : EqP g x) (hh : EqP h y) : EqP (g * h) (mulP x y) := by
  rcases PSL7.mul_pm g h with ⟨p1, p2, p3, p4⟩ | ⟨p1, p2, p3, p4⟩ <;>
  rcases hg with ⟨g1, g2, g3, g4⟩ | ⟨g1, g2, g3, g4⟩ <;>
  rcases hh with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ <;>
  simp only [EqP, mulP, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, p1, p2, p3, p4, g1, g2, g3, g4, h1, h2, h3,
    h4] <;>
  first
  | (refine Or.inl ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | ring1)
  | (refine Or.inr ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | ring1)

theorem eqP_inv {g : PSL7.Grp} {x : N4} (hg : EqP g x) : EqP g⁻¹ (adjP x) := by
  rcases PSL7.inv_pm g with ⟨p1, p2, p3, p4⟩ | ⟨p1, p2, p3, p4⟩ <;>
  rcases hg with ⟨g1, g2, g3, g4⟩ | ⟨g1, g2, g3, g4⟩ <;>
  simp only [EqP, adjP, ZMod.natCast_mod, Nat.cast_mul, Nat.cast_ofNat, six7, p1, p2, p3, p4, g1, g2, g3, g4] <;>
  first
  | (refine Or.inl ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | ring1)
  | (refine Or.inr ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | ring1)

theorem eqS_nest {x1 x2 x3 x4 x5 x6 x7 x8 x9 : SL5.Grp} {n1 n2 n3 n4 n5 n6 n7 n8 n9 : N4}
    (h1 : EqS x1 n1) (h2 : EqS x2 n2) (h3 : EqS x3 n3) (h4 : EqS x4 n4) (h5 : EqS x5 n5)
    (h6 : EqS x6 n6) (h7 : EqS x7 n7) (h8 : EqS x8 n8) (h9 : EqS x9 n9) :
    EqS (x1 * (x2⁻¹ * (x3 * (x4⁻¹ * (x5 * (x6⁻¹ * (x7 * (x8⁻¹ * x9))))))))
      (mulS n1 (mulS (adjS n2) (mulS n3 (mulS (adjS n4) (mulS n5 (mulS (adjS n6) (mulS n7 (mulS (adjS n8) n9)))))))) :=
  eqS_mul h1 (eqS_mul (eqS_inv h2) (eqS_mul h3 (eqS_mul (eqS_inv h4) (eqS_mul h5
    (eqS_mul (eqS_inv h6) (eqS_mul h7 (eqS_mul (eqS_inv h8) h9)))))))

theorem eqP_nest {x1 x2 x3 x4 x5 x6 x7 x8 x9 : PSL7.Grp} {n1 n2 n3 n4 n5 n6 n7 n8 n9 : N4}
    (h1 : EqP x1 n1) (h2 : EqP x2 n2) (h3 : EqP x3 n3) (h4 : EqP x4 n4) (h5 : EqP x5 n5)
    (h6 : EqP x6 n6) (h7 : EqP x7 n7) (h8 : EqP x8 n8) (h9 : EqP x9 n9) :
    EqP (x1 * (x2⁻¹ * (x3 * (x4⁻¹ * (x5 * (x6⁻¹ * (x7 * (x8⁻¹ * x9))))))))
      (mulP n1 (mulP (adjP n2) (mulP n3 (mulP (adjP n4) (mulP n5 (mulP (adjP n6) (mulP n7 (mulP (adjP n8) n9)))))))) :=
  eqP_mul h1 (eqP_mul (eqP_inv h2) (eqP_mul h3 (eqP_mul (eqP_inv h4) (eqP_mul h5
    (eqP_mul (eqP_inv h6) (eqP_mul h7 (eqP_mul (eqP_inv h8) h9)))))))

@@PRODS@@

/-- The `Z_13` part of the nine-letter word of the code `c`: `z₀ - z₁ + z₂ - ⋯ + z₈`, mod `13`. -/
def zc (c : ℕ) : ℕ :=
  (zTab.getD (dig c 0) 0 + 12 * zTab.getD (dig c 1) 0 + zTab.getD (dig c 2) 0 + 12 * zTab.getD (dig c 3) 0
    + zTab.getD (dig c 4) 0 + 12 * zTab.getD (dig c 5) 0 + zTab.getD (dig c 6) 0 + 12 * zTab.getD (dig c 7) 0
    + zTab.getD (dig c 8) 0) % 13

theorem sG_S {j : ℕ} (hj : j < 6) : EqS (sG j).s (sTabS.getD j (1, 0, 0, 1)) := by
  interval_cases j <;> decide

theorem sG_P {j : ℕ} (hj : j < 6) : EqP (sG j).p (sTabP.getD j (1, 0, 0, 1)) := by
  interval_cases j <;> decide

theorem sG_Z {j : ℕ} (hj : j < 6) :
    Multiplicative.toAdd (sG j).z = ((zTab.getD j 0 : ℕ) : ZMod 13) := by
  interval_cases j <;> decide

theorem toAdd_mul13 (x y : Multiplicative (ZMod 13)) :
    Multiplicative.toAdd (x * y) = Multiplicative.toAdd x + Multiplicative.toAdd y := rfl

theorem toAdd_inv13 (x : Multiplicative (ZMod 13)) :
    Multiplicative.toAdd x⁻¹ = -Multiplicative.toAdd x := rfl

theorem eqS_wordC (c : ℕ) : EqS (wordC c).s (prodS c) := by
  have h := eqS_nest (sG_S (dig_lt c 0)) (sG_S (dig_lt c 1)) (sG_S (dig_lt c 2)) (sG_S (dig_lt c 3))
    (sG_S (dig_lt c 4)) (sG_S (dig_lt c 5)) (sG_S (dig_lt c 6)) (sG_S (dig_lt c 7)) (sG_S (dig_lt c 8))
  simp only [wordC, wordOf, mul_s, inv_s, prodS, letS]
  exact h

theorem eqP_wordC (c : ℕ) : EqP (wordC c).p (prodP c) := by
  have h := eqP_nest (sG_P (dig_lt c 0)) (sG_P (dig_lt c 1)) (sG_P (dig_lt c 2)) (sG_P (dig_lt c 3))
    (sG_P (dig_lt c 4)) (sG_P (dig_lt c 5)) (sG_P (dig_lt c 6)) (sG_P (dig_lt c 7)) (sG_P (dig_lt c 8))
  simp only [wordC, wordOf, mul_p, inv_p, prodP, letP]
  exact h

theorem z_wordC (c : ℕ) : Multiplicative.toAdd (wordC c).z = ((zc c : ℕ) : ZMod 13) := by
  simp only [wordC, wordOf, mul_z, inv_z, toAdd_mul13, toAdd_inv13]
  rw [sG_Z (dig_lt c 0), sG_Z (dig_lt c 1), sG_Z (dig_lt c 2), sG_Z (dig_lt c 3), sG_Z (dig_lt c 4),
    sG_Z (dig_lt c 5), sG_Z (dig_lt c 6), sG_Z (dig_lt c 7), sG_Z (dig_lt c 8)]
  simp only [zc, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, twelve13]
  ring

/-- The check of the code `c` against the index `n`. -/
def okN (c n : ℕ) : Bool :=
  decide (cS (prodS c) = SL5.quad (n / 13 / 168)) &&
    decide (cP (prodP c) = PSL7.quad (n / 13 % 168) ∨ cP (prodP c) = negQ7 (PSL7.quad (n / 13 % 168))) &&
    decide (zc c = n % 13)

theorem grpP_fields {n : ℕ} (hn : n < 168) :
    (PSL7.grpP n).a = (PSL7.quad n).1 ∧ (PSL7.grpP n).b = (PSL7.quad n).2.1 ∧
      (PSL7.grpP n).c = (PSL7.quad n).2.2.1 ∧ (PSL7.grpP n).d = (PSL7.quad n).2.2.2 := by
  unfold PSL7.grpP
  rw [dif_pos (PSL7.quad_valid n hn)]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A `PSL(2,7)` element with the entries of `-quad n` has the sign test `false`, so it is not `grpP n`'s class. -/
theorem neg_quad_false (g : PSL7.Grp) {n : ℕ} (hn : n < 168)
    (h1 : g.a = -(PSL7.quad n).1) (h3 : g.c = -(PSL7.quad n).2.2.1) : False := by
  have hq := PSL7.quad_valid n hn
  have hp : PSL7.posB g.a g.c = true := g.pos
  rw [h1, h3, PSL7.posB_neg hq.1, hq.2] at hp
  simp at hp

theorem psl_entries {g : PSL7.Grp} {x : N4} {n : ℕ} (hn : n < 168) (hg : EqP g x)
    (hx : cP x = PSL7.quad n ∨ cP x = negQ7 (PSL7.quad n)) :
    g.a = (PSL7.quad n).1 ∧ g.b = (PSL7.quad n).2.1 ∧ g.c = (PSL7.quad n).2.2.1 ∧ g.d = (PSL7.quad n).2.2.2 := by
  rcases hx with hx | hx
  · have e1 : (x.1 : ZMod 7) = (PSL7.quad n).1 := congrArg Prod.fst hx
    have e2 : (x.2.1 : ZMod 7) = (PSL7.quad n).2.1 := congrArg (fun q => q.2.1) hx
    have e3 : (x.2.2.1 : ZMod 7) = (PSL7.quad n).2.2.1 := congrArg (fun q => q.2.2.1) hx
    have e4 : (x.2.2.2 : ZMod 7) = (PSL7.quad n).2.2.2 := congrArg (fun q => q.2.2.2) hx
    rcases hg with ⟨g1, g2, g3, g4⟩ | ⟨g1, g2, g3, g4⟩
    · exact ⟨g1.trans e1, g2.trans e2, g3.trans e3, g4.trans e4⟩
    · exact (neg_quad_false g hn (g1.trans (by rw [e1])) (g3.trans (by rw [e3]))).elim
  · have e1 : (x.1 : ZMod 7) = -(PSL7.quad n).1 := congrArg Prod.fst hx
    have e2 : (x.2.1 : ZMod 7) = -(PSL7.quad n).2.1 := congrArg (fun q => q.2.1) hx
    have e3 : (x.2.2.1 : ZMod 7) = -(PSL7.quad n).2.2.1 := congrArg (fun q => q.2.2.1) hx
    have e4 : (x.2.2.2 : ZMod 7) = -(PSL7.quad n).2.2.2 := congrArg (fun q => q.2.2.2) hx
    rcases hg with ⟨g1, g2, g3, g4⟩ | ⟨g1, g2, g3, g4⟩
    · exact (neg_quad_false g hn (g1.trans e1) (g3.trans e3)).elim
    · exact ⟨g1.trans (by rw [e1, neg_neg]), g2.trans (by rw [e2, neg_neg]),
        g3.trans (by rw [e3, neg_neg]), g4.trans (by rw [e4, neg_neg])⟩

theorem okN_spec {c n : ℕ} (hn : n < 262080) (h : okN c n = true) : gOf n = wordC c := by
  unfold okN at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hS, hP⟩, hZ⟩ := h
  have hn1 : n / 13 / 168 < 120 := by omega
  have hn2 : n / 13 % 168 < 168 := Nat.mod_lt _ (by norm_num)
  obtain ⟨s1, s2, s3, s4⟩ := eqS_wordC c
  -- `prodS c` is opaque from here on: projecting it would unfold the nested products (exponentially)
  generalize prodS c = Q at hS s1 s2 s3 s4
  have e1 : (Q.1 : ZMod 5) = (SL5.quad (n / 13 / 168)).1 := congrArg Prod.fst hS
  have e2 : (Q.2.1 : ZMod 5) = (SL5.quad (n / 13 / 168)).2.1 := congrArg (fun q => q.2.1) hS
  have e3 : (Q.2.2.1 : ZMod 5) = (SL5.quad (n / 13 / 168)).2.2.1 := congrArg (fun q => q.2.2.1) hS
  have e4 : (Q.2.2.2 : ZMod 5) = (SL5.quad (n / 13 / 168)).2.2.2 := congrArg (fun q => q.2.2.2) hS
  have hPsl := psl_entries hn2 (eqP_wordC c) hP
  have hgrp := grpP_fields hn2
  refine G.ext ?_ ?_ ?_
  · refine SL5.Grp.ext ?_ ?_ ?_ ?_
    · exact (SL5.grpOf_fields hn1).1.trans (s1.trans e1).symm
    · exact (SL5.grpOf_fields hn1).2.1.trans (s2.trans e2).symm
    · exact (SL5.grpOf_fields hn1).2.2.1.trans (s3.trans e3).symm
    · exact (SL5.grpOf_fields hn1).2.2.2.trans (s4.trans e4).symm
  · refine PSL7.Grp.ext ?_ ?_ ?_ ?_
    · exact hgrp.1.trans hPsl.1.symm
    · exact hgrp.2.1.trans hPsl.2.1.symm
    · exact hgrp.2.2.1.trans hPsl.2.2.1.symm
    · exact hgrp.2.2.2.trans hPsl.2.2.2.symm
  · apply Multiplicative.toAdd.injective
    rw [z_wordC c, hZ]
    rfl

/-- The code in position `i` of a stage table `C`: 24 bits each. -/
def codeAt (C i : ℕ) : ℕ := (C >>> (24 * i)) % 16777216

/-- The stage check: the codes of the table `C` pass `okN` at the indices `base … base + len - 1`. -/
def chkN (base len C : ℕ) : Bool :=
  (List.range len).all (fun i => okN (codeAt C i) (base + i))

theorem chkN_ex (base len C : ℕ) (h : chkN base len C = true) (n : ℕ) (hn : base ≤ n) (hn' : n < base + len)
    (hN : n < 262080) : ∃ c, gOf n = wordC c := by
  refine ⟨codeAt C (n - base), okN_spec hN ?_⟩
  have h2 : okN (codeAt C (n - base)) (base + (n - base)) = true :=
    List.all_eq_true.mp h (n - base) (List.mem_range.mpr (by omega))
  have e : base + (n - base) = n := by omega
  rw [e] at h2
  exact h2

end BipartiteDD.Haar.D6D10d
"""


def natcheck_module(S):
    sl = ", ".join("(%d, %d, %d, %d)" % X for X, _, _ in S)
    ps = ", ".join("(%d, %d, %d, %d)" % canon7(Y) for _, Y, _ in S)
    zs = ", ".join(str(z) for _, _, z in S)
    return (NATCHECK.replace("@@SL@@", sl).replace("@@PS@@", ps).replace("@@Z@@", zs)
            .replace("@@PRODS@@", prod_lean()))


def stage_module(k, codes):
    lo = k * STAGE
    packed = 0
    for i in range(STAGE):
        c = int(codes[lo + i])
        assert 0 <= c < 2 ** BITS
        packed |= c << (BITS * i)
    return f"""import BipartiteDD.Haar.D6D10d.NatCheck

/-! Certificates for the (6,10) record on 524,160 vertices, stage {k:02d} of {NSTAGES}: the indices
`{lo} ≤ n < {lo + STAGE}`. Generated by research/lean-haarD/gen_d6D10d.py. Do not edit by hand. -/

namespace BipartiteDD.Haar.D6D10d

def stageC{k:02d} : ℕ := 0x{packed:x}

set_option maxRecDepth 100000 in
theorem certC{k:02d} : chkN {lo} {STAGE} stageC{k:02d} = true := by decide +kernel

end BipartiteDD.Haar.D6D10d
"""


def cover_module():
    imports = "\n".join("import BipartiteDD.Haar.D6D10d.Stage%02d" % k for k in range(NSTAGES))
    ors = " ∨ ".join("k = %d" % k for k in range(NSTAGES))
    alts = " | ".join("h%d" % k for k in range(NSTAGES))
    cases = "\n".join(
        "  · exact chkN_ex %d %d stageC%02d certC%02d n (by omega) (by omega) hn" % (k * STAGE, STAGE, k, k)
        for k in range(NSTAGES))
    return f"""import BipartiteDD.Haar.D6D10d.NatCheck
{imports}

/-! Every index `n < 262080` has a covering word, by the stage checks. Generated by
research/lean-haarD/gen_d6D10d.py. Do not edit by hand. -/

namespace BipartiteDD.Haar.D6D10d

theorem exC (n : ℕ) (hn : n < 262080) : ∃ c, gOf n = wordC c := by
  obtain ⟨k, hk⟩ : ∃ k, n / {STAGE} = k := ⟨_, rfl⟩
  have hk47 : k < {NSTAGES} := by omega
  rcases (show {ors} by omega) with {alts}
{cases}

end BipartiteDD.Haar.D6D10d
"""


COVERING = """import BipartiteDD.Haar.D6D10d.Cover

/-! The covering hypothesis `CoverHyp SS` of the Δ6·D10 record, from the stage checks of `Cover`. -/

namespace BipartiteDD.Haar.D6D10d

theorem cover : CoverHyp SS := by
  unfold CoverHyp
  intro g
  obtain ⟨c, hc⟩ := exC (idxG g) (idxG_lt g)
  rw [gOf_idxG] at hc
  refine ⟨sG (dig c 0), sG_mem _ (dig_lt c 0), sG (dig c 1), sG_mem _ (dig_lt c 1),
    sG (dig c 2), sG_mem _ (dig_lt c 2), sG (dig c 3), sG_mem _ (dig_lt c 3),
    sG (dig c 4), sG_mem _ (dig_lt c 4), sG (dig c 5), sG_mem _ (dig_lt c 5),
    sG (dig c 6), sG_mem _ (dig_lt c 6), sG (dig c 7), sG_mem _ (dig_lt c 7),
    sG (dig c 8), sG_mem _ (dig_lt c 8), ?_⟩
  exact hc

end BipartiteDD.Haar.D6D10d
"""

RECORD = """import BipartiteDD.Haar.D6D10d.Covering
import BipartiteDD.Haar.Diam10

/-! The (6,10) record on 524,160 vertices: the Haar graph of `SL(2,5) × PSL(2,7) × Z_13` with the connection set `S`
of `research/frontier/sols/d6D10_prod_sl_5_psl_7_13_orb3f0_s1.txt`. The covering hypothesis is `D6D10d.cover`. -/

open BipartiteDD.Haar.D6D10d in
/-- A graph on 524160 vertices, bipartite, of degree at most 6 and diameter at most 10. -/
theorem nb_6_10_524160 : ∃ G : SimpleGraph (Fin 524160), BipartiteDD.IsBipartiteDegDiam G 6 10 := by
  have h := BipartiteDD.Haar.haar_isBipartiteDegDiam10_of_equiv SS haarVert cover
  rw [card_SS] at h
  exact ⟨_, h⟩
"""

AXIOMS = """import BipartiteDD.Haar.D6D10d.Record

#print axioms nb_6_10_524160
"""


def main():
    sol, outdir = sys.argv[1], sys.argv[2]
    S = parse_sol(sol)
    codes = find_codes(S)
    verify(S, codes)
    os.makedirs(outdir, exist_ok=True)

    def write(name, text):
        with open(os.path.join(outdir, name), "w") as f:
            f.write(text)

    write("SL5.lean", template_sl5(open(SRC_SL19).read()))
    write("PSL7.lean", template_psl7(open(SRC_PSL19).read()))
    write("Base.lean", BASE)
    write("Words.lean", WORDS)
    write("Gens.lean", gens_module(S))
    write("Check.lean", CHECK)
    write("NatCheck.lean", natcheck_module(S))
    for k in range(NSTAGES):
        write("Stage%02d.lean" % k, stage_module(k, codes))
    write("Cover.lean", cover_module())
    write("Covering.lean", COVERING)
    write("Record.lean", RECORD)
    write("Axioms.lean", AXIOMS)
    print("ok: all", N, "elements certified; stages", NSTAGES, flush=True)


if __name__ == "__main__":
    main()
