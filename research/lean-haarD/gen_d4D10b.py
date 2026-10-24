#!/usr/bin/env python3
"""Covering certificate for the (4,10) record on 12,416 vertices (job d4D10b).

G = Z_97 x|_19 Z_64 (order 6,208, the metacyclic rule (a,j)(b,l) = (a + 19^j b, j + l) mod (97, 64)), S = the 4 elements of
research/lifts/sols/d4D10_n12416_haar_meta97_64_19.txt. The diameter bound is Haar/Diam10.lean
(haar_isBipartiteDegDiam10_of_equiv), fed the nine-letter covering hypothesis `CoverHyp` of Haar/D4D10b/Words.lean.

Covering words. Nine letters x1 x2⁻¹ x3 x4⁻¹ x5 x6⁻¹ x7 x8⁻¹ x9 with digits d_i in range(4): letter i is S[d_i],
inverted for odd i (0-based). The code of a word is sum_i d_i 4^i (18 bits). Entry n of a stage table is the least code
whose word is the element with index n = x * 64 + y (Lean: `enc`). Every word is re-checked by direct multiplication
before any Lean file is written. Stage tables: 16 stages of 388 codes (16 * 388 = 6,208).

Writes, under OUT (default lean/BipartiteDD/Haar/D4D10b): Words.lean, Meta97.lean, Check.lean, Stage00..Stage15.lean,
Cover.lean, Record.lean, Axioms.lean. Axioms.out.txt is written by hand from `lake env lean Axioms.lean`.

Usage: python3 research/lean-haarD/gen_d4D10b.py [OUT]
"""
import os
import re
import sys

REPO = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
SOL = os.path.join(REPO, "research", "lifts", "sols", "d4D10_n12416_haar_meta97_64_19.txt")

M, K, R = 97, 64, 19          # Z_97 x|_19 Z_64
N = M * K                     # 6,208 elements
NREC = 2 * N                  # 12,416 vertices
NS = 4                        # degree
L = 9                         # letters per word
BASE = 4                      # digits per letter
BITS = 18                     # 4 ** 9 = 2 ** 18
STAGES = 16
SIZE = N // STAGES            # 388
MOD = "D4D10b"
NS_LEAN = "BipartiteDD.Haar.D4D10b"


def group():
    assert pow(R, K, M) == 1, "r^k must be 1 mod m"

    def mul(x, y):
        return ((x[0] + pow(R, x[1], M) * y[0]) % M, (x[1] + y[1]) % K)

    def inv(x):
        l = (-x[1]) % K
        return ((-pow(R, l, M) * x[0]) % M, l)

    return mul, inv


def parse_sol(path):
    lines = [ln.strip() for ln in open(path) if ln.strip()]
    gl = [ln.split() for ln in lines if ln.startswith("group ")]
    assert gl == [["group", "meta", str(M), str(K), str(R)]], gl
    S = []
    for ln in lines:
        mt = re.fullmatch(r"e 0 1 = (\d+),(\d+)", ln)
        if mt:
            S.append((int(mt.group(1)), int(mt.group(2))))
    assert len(S) == NS and len(set(S)) == NS, S
    for a, j in S:
        assert 0 <= a < M and 0 <= j < K, (a, j)
    return S


def exponents():
    return [1 if i % 2 == 0 else -1 for i in range(L)]


def word_value(mul, inv, S, digs):
    el = (0, 0)
    for d, e in zip(digs, exponents()):
        el = mul(el, S[d] if e == 1 else inv(S[d]))
    return el


def find_codes(mul, inv, S):
    """Least code of a word for each index n < N, every word checked by direct multiplication."""
    seen = {}
    for code in range(BASE ** L):
        digs = [(code // BASE ** i) % BASE for i in range(L)]
        el = word_value(mul, inv, S, digs)
        seen.setdefault(el[0] * K + el[1], code)
    assert len(seen) == N, ("uncovered", N - len(seen))
    codes = [seen[n] for n in range(N)]
    for n, code in enumerate(codes):
        digs = [(code // BASE ** i) % BASE for i in range(L)]
        assert word_value(mul, inv, S, digs) == (n // K, n % K), n
    return codes


def letter(i):
    return f"(sel (digit c {i}))⁻¹" if i % 2 == 1 else f"sel (digit c {i})"


def write(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w") as f:
        f.write(text)
    print("wrote", os.path.relpath(path, REPO))


def words_module():
    return f"""import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Finset.Basic

/-! The nine-letter covering word and its covering hypothesis, for a general group.

`wordOf x₁ … x₉` is `x₁ x₂⁻¹ x₃ x₄⁻¹ x₅ x₆⁻¹ x₇ x₈⁻¹ x₉`, right-nested. `CoverHyp S` is the hypothesis of
`BipartiteDD.Haar.haar_isBipartiteDegDiam10_of_equiv` (`Haar/Diam10.lean`) written with the same group operations, so
the record passes a proof of `CoverHyp SS` directly (see research/lean-haarD/BRIEF.md, the `CoverHyp` fix). -/

namespace {NS_LEAN}

/-- The nine-letter alternating word, right-nested. -/
def wordOf {{G : Type*}} [Group G] (x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ : G) : G :=
  x₁ * (x₂⁻¹ * (x₃ * (x₄⁻¹ * (x₅ * (x₆⁻¹ * (x₇ * (x₈⁻¹ * x₉)))))))

/-- Every element of `G` is a nine-letter word in `S` (the covering condition of `Diam10`). -/
def CoverHyp {{G : Type*}} [Group G] (S : Finset G) : Prop :=
  ∀ g : G, ∃ x₁ ∈ S, ∃ x₂ ∈ S, ∃ x₃ ∈ S, ∃ x₄ ∈ S, ∃ x₅ ∈ S, ∃ x₆ ∈ S, ∃ x₇ ∈ S, ∃ x₈ ∈ S,
    ∃ x₉ ∈ S, g = x₁ * (x₂⁻¹ * (x₃ * (x₄⁻¹ * (x₅ * (x₆⁻¹ * (x₇ * (x₈⁻¹ * x₉)))))))

end {NS_LEAN}
"""


def meta_module():
    return f"""import Mathlib.Algebra.Group.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-! The group `Z_{M} ⋊ Z_{K}` of the (4,10) record on {NREC} vertices.

Elements are pairs `(x, y)` with `x ∈ ZMod {M}` and `y ∈ ZMod {K}`, with product
`(x, y) * (x', y') = (x + {R} ^ y.val * x', y + y')`. This is the rule `(a,j)(b,l) = (a + r^j b, j + l)` of
`research/frontier/haar_gen3.c` with `r = {R}`. The map `y ↦ {R} ^ y.val` is a homomorphism `ZMod {K} → ZMod {M}`
because `{R} ^ {K} = 1` in `ZMod {M}` (the order of {R} is 32, which divides {K}); `tw_add` checks this on all pairs.

The index of `(x, y)` is `x.val * {K} + y.val`, in `[0, {N})`. -/

namespace {NS_LEAN}.Meta97

/-- The twist `{R} ^ y` for `y : ZMod {K}`. -/
def tw (y : ZMod {K}) : ZMod {M} := {R} ^ y.val

theorem tw_zero : tw 0 = 1 := by decide

theorem tw_add : ∀ y z : ZMod {K}, tw (y + z) = tw y * tw z := by decide +kernel

/-- Elements of `Z_{M} ⋊ Z_{K}`. -/
@[ext] structure Grp where
  x : ZMod {M}
  y : ZMod {K}
  deriving DecidableEq

instance : Group Grp where
  mul p q := ⟨p.x + tw p.y * q.x, p.y + q.y⟩
  one := ⟨0, 0⟩
  inv p := ⟨-(tw (-p.y) * p.x), -p.y⟩
  mul_assoc a b c := by
    ext
    · show a.x + tw a.y * b.x + tw (a.y + b.y) * c.x = a.x + tw a.y * (b.x + tw b.y * c.x)
      rw [tw_add]
      ring
    · show a.y + b.y + c.y = a.y + (b.y + c.y)
      exact add_assoc _ _ _
  one_mul a := by
    ext
    · show 0 + tw 0 * a.x = a.x
      rw [tw_zero]
      ring
    · show 0 + a.y = a.y
      exact zero_add _
  mul_one a := by
    ext
    · show a.x + tw a.y * 0 = a.x
      ring
    · show a.y + 0 = a.y
      exact add_zero _
  inv_mul_cancel a := by
    ext
    · show -(tw (-a.y) * a.x) + tw (-a.y) * a.x = 0
      ring
    · show -a.y + a.y = 0
      exact neg_add_cancel _

/-- The index of an element: `x.val * {K} + y.val`, in `[0, {N})`. -/
def enc (g : Grp) : ℕ := g.x.val * {K} + g.y.val

/-- The element with index `n`: `(n / {K}, n % {K})`. Inverse to `enc` on `n < {N}`. -/
def grpOf (n : ℕ) : Grp := ⟨(n / {K} : ℕ), (n % {K} : ℕ)⟩

theorem enc_lt (g : Grp) : enc g < {N} := by
  have h1 := ZMod.val_lt g.x
  have h2 := ZMod.val_lt g.y
  unfold enc
  omega

theorem grpOf_enc (g : Grp) : grpOf (enc g) = g := by
  have h2 := ZMod.val_lt g.y
  have hd : (g.x.val * {K} + g.y.val) / {K} = g.x.val := by omega
  have hm : (g.x.val * {K} + g.y.val) % {K} = g.y.val := by omega
  unfold grpOf enc
  rw [hd, hm, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

theorem enc_grpOf {{n : ℕ}} (hn : n < {N}) : enc (grpOf n) = n := by
  unfold enc grpOf
  have h1 : (n / {K} : ℕ) = (n / {K}) % {M} := (Nat.mod_eq_of_lt (by omega)).symm
  simp only [ZMod.val_natCast]
  rw [← h1, Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num))]
  omega

/-- The numbering `Grp ≃ Fin {N}` of `Z_{M} ⋊ Z_{K}`. -/
def equivG : Grp ≃ Fin {N} where
  toFun g := ⟨enc g, enc_lt g⟩
  invFun n := grpOf n.val
  left_inv g := grpOf_enc g
  right_inv n := Fin.ext (enc_grpOf n.isLt)

end {NS_LEAN}.Meta97
"""


def check_module(S):
    svec = ", ".join(f"⟨{a}, {j}⟩" for a, j in S)
    return f"""import BipartiteDD.Haar.D4D10b.Meta97
import BipartiteDD.Haar.D4D10b.Words

/-! Covering certificates of the (4,10) record on {NREC} vertices: the Haar graph of `Meta97` with the connection set
`S` of `research/lifts/sols/d4D10_n12416_haar_meta97_64_19.txt` (degree {NS}).

For an index `n < {N}` the code `c` of a word holds {L} base-{BASE} digits, and letter `i` of the word is `sel (digit c i)`,
inverted for odd `i` by `wordOf`. A stage table packs `{SIZE}` codes of `{BITS}` bits each. Generated by
research/lean-haarD/gen_d4D10b.py; do not edit by hand. -/

namespace {NS_LEAN}

open {NS_LEAN}.Meta97

/-- The connection set `S`, as elements `(x, y)` of `Meta97`, in the order of the sol file. -/
def sVec : List Grp :=
  [{svec}]

/-- The `j`-th element of `S`. -/
def sel (j : ℕ) : Grp := sVec.getD j 1

/-- `S` as a finset. -/
def SS : Finset Grp := sVec.toFinset

theorem card_SS : SS.card = {NS} := by decide +kernel

theorem sel_mem_all : (List.range {NS}).all (fun j => decide (sel j ∈ SS)) = true := by
  decide +kernel

theorem sel_mem (j : ℕ) (hj : j < {NS}) : sel j ∈ SS := by
  have h := List.all_eq_true.mp sel_mem_all j (List.mem_range.mpr hj)
  simpa using h

/-- The digit `k` of the code `c`, in base {BASE}. -/
def digit (c k : ℕ) : ℕ := c / {BASE} ^ k % {BASE}

theorem digit_lt (c k : ℕ) : digit c k < {BASE} := Nat.mod_lt _ (by norm_num)

/-- The nine-letter word of the code `c`. -/
def wordD (c : ℕ) : Grp :=
  wordOf (sel (digit c 0)) (sel (digit c 1)) (sel (digit c 2)) (sel (digit c 3)) (sel (digit c 4))
    (sel (digit c 5)) (sel (digit c 6)) (sel (digit c 7)) (sel (digit c 8))

def okD (c n : ℕ) : Bool := decide (grpOf n = wordD c)

/-- A stage table is a natural number `C` holding codes of `{BITS}` bits, the code `i` in bits
`[{BITS} * i, {BITS} * i + {BITS})`. -/
def codeAt (C i : ℕ) : ℕ := (C >>> ({BITS} * i)) % {2 ** BITS}

def chkD (base len C : ℕ) : Bool :=
  (List.range len).all (fun i => okD (codeAt C i) (base + i))

theorem stageExD (base len C : ℕ) (h : chkD base len C = true) (n : ℕ) (hn : base ≤ n)
    (hn' : n < base + len) : ∃ c, okD c n = true := by
  refine ⟨codeAt C (n - base), ?_⟩
  have := List.all_eq_true.mp h (n - base) (List.mem_range.mpr (by omega))
  rwa [show base + (n - base) = n by omega] at this

end {NS_LEAN}
"""


def stage_module(idx, table):
    base = idx * SIZE
    C = 0
    for i, code in enumerate(table):
        C |= code << (BITS * i)
    st = f"stageD{idx:02d}"
    ce = f"certD{idx:02d}"
    return f"""import BipartiteDD.Haar.D4D10b.Check

/-! Covering certificates, stage {idx:02d} of {STAGES}: the indices `{base} ≤ n < {base + SIZE}` of the (4,10) record on
`Meta97`. `{st}` packs the codes of the elements with those indices: the code of index `{base} + i` is `codeAt {st} i`.
Generated by research/lean-haarD/gen_d4D10b.py; do not edit by hand. -/

namespace {NS_LEAN}

def {st} : ℕ := 0x{C:x}

set_option maxRecDepth 100000 in
theorem {ce} : chkD {base} {SIZE} {st} = true := by decide +kernel

end {NS_LEAN}
"""


def cover_module():
    stages = list(range(STAGES))
    imports = ["import BipartiteDD.Haar.D4D10b.Check", "import BipartiteDD.Haar.D4D10b.Words"]
    imports += [f"import BipartiteDD.Haar.D4D10b.Stage{s:02d}" for s in stages]
    ks = " ∨ ".join(f"k = {s}" for s in stages)
    hs = " | ".join(f"h{s}" for s in stages)
    cases = "\n".join(
        f"  · exact stageExD {s * SIZE} {SIZE} stageD{s:02d} certD{s:02d} n (by omega) (by omega)" for s in stages
    )
    sel_args = ", ".join(f"sel (digit c {i}), sel_mem _ (digit_lt c {i})" for i in range(L))
    return "\n".join(imports) + f"""

/-! The covering hypothesis of the (4,10) record on `Meta97`: every element is a nine-letter word in `SS`, by the
kernel-checked certificates of the stage modules. `cover : CoverHyp SS` is the hypothesis of
`haar_isBipartiteDegDiam10_of_equiv`. Generated by research/lean-haarD/gen_d4D10b.py; do not edit by hand. -/

namespace {NS_LEAN}

open {NS_LEAN}.Meta97

theorem exD (n : ℕ) (hn : n < {N}) : ∃ c, okD c n = true := by
  obtain ⟨k, hk⟩ : ∃ k, n / {SIZE} = k := ⟨_, rfl⟩
  rcases (show {ks} by omega) with {hs}
{cases}

theorem cover : CoverHyp SS := by
  unfold CoverHyp
  intro g
  obtain ⟨c, hc⟩ := exD (enc g) (enc_lt g)
  have h : grpOf (enc g) = wordD c := of_decide_eq_true hc
  rw [grpOf_enc] at h
  exact ⟨{sel_args}, h⟩

end {NS_LEAN}
"""


def record_module():
    return f"""import BipartiteDD.Haar.D4D10b.Cover
import BipartiteDD.Haar.Diam10

/-! The (4,10) lift record on {NREC} vertices: the Haar graph of `Meta97` (order {N}) with the connection set of
`research/lifts/sols/d4D10_n12416_haar_meta97_64_19.txt`. The covering hypothesis is `cover : CoverHyp SS`, and the
diameter-10 lemma is `BipartiteDD.Haar.haar_isBipartiteDegDiam10_of_equiv` (`Haar/Diam10.lean`). -/

namespace {NS_LEAN}

open BipartiteDD.Haar

/-- `(Meta97 ⊕ Meta97) ≃ Fin {NREC}`: the two sides, numbered `0 … {NREC - 1}`. -/
noncomputable def equiv{NREC} : Meta97.Grp ⊕ Meta97.Grp ≃ Fin {NREC} :=
  (Equiv.sumCongr Meta97.equivG Meta97.equivG).trans (finSumFinEquiv.trans (finCongr (by norm_num)))

/-- The Haar graph of `SS`, transported to `Fin {NREC}`. -/
noncomputable def G{NREC} : SimpleGraph (Fin {NREC}) := (haarGraph SS).comap equiv{NREC}.symm

theorem isBipartiteDegDiam_G{NREC} : BipartiteDD.IsBipartiteDegDiam G{NREC} 4 10 := by
  have h := haar_isBipartiteDegDiam10_of_equiv SS equiv{NREC} cover
  rw [card_SS] at h
  exact h

end {NS_LEAN}

open {NS_LEAN} in
/-- A bipartite graph on {NREC} vertices with degree at most 4 and diameter at most 10. -/
theorem nb_4_10_{NREC} : ∃ H : SimpleGraph (Fin {NREC}), BipartiteDD.IsBipartiteDegDiam H 4 10 :=
  ⟨G{NREC}, isBipartiteDegDiam_G{NREC}⟩
"""


def axioms_module():
    return f"""-- Axioms of the (4,10) record on {NREC} vertices (job d4D10b). The line should list only
-- [propext, Classical.choice, Quot.sound].
import BipartiteDD.Haar.D4D10b.Record

#print axioms nb_4_10_{NREC}
"""


def main():
    out = sys.argv[1] if len(sys.argv) > 1 else os.path.join(REPO, "lean", "BipartiteDD", "Haar", MOD)
    mul, inv = group()
    S = parse_sol(SOL)
    codes = find_codes(mul, inv, S)
    write(os.path.join(out, "Words.lean"), words_module())
    write(os.path.join(out, "Meta97.lean"), meta_module())
    write(os.path.join(out, "Check.lean"), check_module(S))
    for s in range(STAGES):
        write(os.path.join(out, f"Stage{s:02d}.lean"), stage_module(s, codes[s * SIZE:(s + 1) * SIZE]))
    write(os.path.join(out, "Cover.lean"), cover_module())
    write(os.path.join(out, "Record.lean"), record_module())
    write(os.path.join(out, "Axioms.lean"), axioms_module())


if __name__ == "__main__":
    main()
