#!/usr/bin/env python3
"""Covering certificates for the two lift records of job lift58410.

  D5D8:  delta 5, diameter 8, 9,576 vertices. G = Z_266 x|_17 Z_18 (order 4,788); S = the 5 elements of
         research/lifts/sols/d5D8_n9576_haar_meta266_18_17.txt. Diameter by Haar/Diam8.lean (isBipartiteDegDiam8_of).
  D4D10: delta 4, diameter 10, 12,246 vertices. G = Z_157 x|_9 Z_39 (order 6,123); S = the 4 elements of
         research/lifts/sols/d4D10_n12246_haar_meta157_39_9.txt. Diameter by Haar/Diam10.lean (haar_isBipartiteDegDiam10_of_equiv).

Numbering (as in LiftA/Meta266.lean and LiftA/Meta157.lean): (a, j) has index a * k + j, and
(a, j)(b, l) = (a + r^j b, j + l) mod (m, k), the rule of research/frontier/haar_gen3.c.

Covering words. A word of length L is S[d_0]^e_0 ... S[d_{L-1}]^e_{L-1}, with digits d_i in range(|S|) and
exponents e_i = -1 or +1:
  side A  (D5D8 hA: 4 pairs a1⁻¹ b1 ... a4⁻¹ b4):           e_i = -1 for even i, +1 for odd i   (L = 8)
  side B  (D5D8 hB: 4 pairs a1 b1⁻¹ ... a4 b4⁻¹):           e_i = +1 for even i, -1 for odd i   (L = 8)
  side C  (D5D8 hAB: 3 pairs then s, a1 b1⁻¹ ... a3 b3⁻¹ s): e_i = +1 for even i, -1 for odd i   (L = 7)
  side D  (D4D10 hC: x1 x2⁻¹ x3 ... x8⁻¹ x9):                e_i = +1 for even i, -1 for odd i   (L = 9)
The code of a word is sum_i d_i |S|^i, stored in `bits` bits. Entry n of a table is the least code of a word equal to
the element with index n. Every word is re-checked by direct multiplication below.

Usage: python3 research/lean-haarD/gen_lift58410.py [OUT]
(default OUT = lean/BipartiteDD/Haar/LiftA). Writes Meta266.lean, Meta157.lean, D5D8/ and D4D10/ (Check, Stage*,
Cover, Record). Axioms.lean and Axioms.out.txt are written by hand.
"""
import itertools
import os
import re
import sys

REPO = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
SOLS = os.path.join(REPO, "research", "lifts", "sols")

RECORDS = {
    "D5D8": dict(
        sol="d5D8_n9576_haar_meta266_18_17.txt", m=266, k=18, r=17, ns=5, N=4788,
        nrec=9576, delta=5, D=8, stages=12, bits=19, base=5,
        covers=[("A", 8, "A"), ("B", 8, "B"), ("C", 7, "B")],
        grp="Meta266", mod="D5D8",
    ),
    "D4D10": dict(
        sol="d4D10_n12246_haar_meta157_39_9.txt", m=157, k=39, r=9, ns=4, N=6123,
        nrec=12246, delta=4, D=10, stages=13, bits=18, base=4,
        covers=[("D", 9, "B")],
        grp="Meta157", mod="D4D10",
    ),
}


def group(m, k, r):
    assert pow(r, k, m) == 1, (m, k, r)

    def mul(x, y):
        return ((x[0] + pow(r, x[1], m) * y[0]) % m, (x[1] + y[1]) % k)

    def inv(x):
        l = (-x[1]) % k
        return ((-pow(r, l, m) * x[0]) % m, l)

    return mul, inv


def parse_sol(path, spec):
    lines = [ln.strip() for ln in open(path) if ln.strip()]
    gl = [ln.split() for ln in lines if ln.startswith("group ")]
    assert gl == [["group", "meta", str(spec["m"]), str(spec["k"]), str(spec["r"])]], gl
    S = []
    for ln in lines:
        mt = re.fullmatch(r"e 0 1 = (\d+),(\d+)", ln)
        if mt:
            S.append((int(mt.group(1)), int(mt.group(2))))
    assert len(S) == spec["ns"] and len(set(S)) == spec["ns"], S
    for a, j in S:
        assert 0 <= a < spec["m"] and 0 <= j < spec["k"], (a, j)
    return S


def exponents(side, L):
    if side == "A":
        return [-1 if i % 2 == 0 else 1 for i in range(L)]
    return [1 if i % 2 == 0 else -1 for i in range(L)]


def word_value(mul, inv, S, digs, exps):
    el = (0, 0)
    for d, e in zip(digs, exps):
        el = mul(el, S[d] if e == 1 else inv(S[d]))
    return el


def find_codes(mul, inv, S, spec, L, side):
    """Least code of a word of length L for each index n < N (checked by direct multiplication)."""
    base, N, k = spec["base"], spec["N"], spec["k"]
    exps = exponents(side, L)
    seen = {}
    for code in range(base ** L):
        digs = [(code // base ** i) % base for i in range(L)]
        el = word_value(mul, inv, S, digs, exps)
        idx = el[0] * k + el[1]
        if idx not in seen:
            seen[idx] = code
    assert len(seen) == N, ("uncovered", side, N - len(seen))
    codes = [seen[n] for n in range(N)]
    for n, code in enumerate(codes):
        digs = [(code // base ** i) % base for i in range(L)]
        assert word_value(mul, inv, S, digs, exps) == (n // k, n % k), (side, n)
    return codes


def hexlit(x):
    return "0x" + format(x, "x")


def letter(i, e):
    return f"(sel (digit c {i}))⁻¹" if e == -1 else f"sel (digit c {i})"


def word_pairs(L, exps):
    """Diam8 shape: first pair left-associated, later pairs parenthesized, a last letter if L is odd."""
    parts = []
    for p in range(L // 2):
        a, b = letter(2 * p, exps[2 * p]), letter(2 * p + 1, exps[2 * p + 1])
        parts.append(f"{a} * {b}" if p == 0 else f"({a} * {b})")
    if L % 2 == 1:
        parts.append(letter(L - 1, exps[L - 1]))
    return " * ".join(parts)


def word_nested(L, exps):
    """Diam10 shape x₁ * (x₂⁻¹ * (x₃ * ... (x₈⁻¹ * x₉)))."""

    def nest(i):
        if i == L - 1:
            return letter(i, exps[i])
        return f"{letter(i, exps[i])} * ({nest(i + 1)})"

    return nest(0)


def write(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w") as f:
        f.write(text)
    print("wrote", os.path.relpath(path, REPO))


def meta_module(spec):
    m, k, r, N, nrec = spec["m"], spec["k"], spec["r"], spec["N"], spec["nrec"]
    name = spec["grp"]
    return f"""import Mathlib.Algebra.Group.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-! The group `Z_{m} ⋊ Z_{k}` of a lift record on {nrec} vertices.

Elements are pairs `(x, y)` with `x ∈ ZMod {m}` and `y ∈ ZMod {k}`, with product
`(x, y) * (x', y') = (x + {r} ^ y.val * x', y + y')`. This is the rule `(a,j)(b,l) = (a + r^j b, j + l)` of
`research/frontier/haar_gen3.c` with `r = {r}`. The map `y ↦ {r} ^ y.val` is a homomorphism `ZMod {k} → ZMod {m}`
because `{r} ^ {k} = 1` in `ZMod {m}`; `tw_add` checks this on all pairs.

The index of `(x, y)` is `x.val * {k} + y.val`, in `[0, {N})`. -/

namespace BipartiteDD.Haar.LiftA.{name}

/-- The twist `{r} ^ y` for `y : ZMod {k}`. -/
def tw (y : ZMod {k}) : ZMod {m} := {r} ^ y.val

theorem tw_zero : tw 0 = 1 := by decide

theorem tw_add : ∀ y z : ZMod {k}, tw (y + z) = tw y * tw z := by decide +kernel

/-- Elements of `Z_{m} ⋊ Z_{k}`. -/
@[ext] structure Grp where
  x : ZMod {m}
  y : ZMod {k}
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

/-- The index of an element: `x.val * {k} + y.val`, in `[0, {N})`. -/
def enc (g : Grp) : ℕ := g.x.val * {k} + g.y.val

/-- The element with index `n`: `(n / {k}, n % {k})`. Inverse to `enc` on `n < {N}`. -/
def grpOf (n : ℕ) : Grp := ⟨(n / {k} : ℕ), (n % {k} : ℕ)⟩

theorem enc_lt (g : Grp) : enc g < {N} := by
  have h1 := ZMod.val_lt g.x
  have h2 := ZMod.val_lt g.y
  unfold enc
  omega

theorem grpOf_enc (g : Grp) : grpOf (enc g) = g := by
  have h2 := ZMod.val_lt g.y
  have hd : (g.x.val * {k} + g.y.val) / {k} = g.x.val := by omega
  have hm : (g.x.val * {k} + g.y.val) % {k} = g.y.val := by omega
  unfold grpOf enc
  rw [hd, hm, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

theorem enc_grpOf {{n : ℕ}} (hn : n < {N}) : enc (grpOf n) = n := by
  unfold enc grpOf
  have h1 : (n / {k} : ℕ) = (n / {k}) % {m} := (Nat.mod_eq_of_lt (by omega)).symm
  simp only [ZMod.val_natCast]
  rw [← h1, Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num))]
  omega

/-- The numbering `Grp ≃ Fin {N}` of `Z_{m} ⋊ Z_{k}`. -/
def equivG : Grp ≃ Fin {N} where
  toFun g := ⟨enc g, enc_lt g⟩
  invFun n := grpOf n.val
  left_inv g := grpOf_enc g
  right_inv n := Fin.ext (enc_grpOf n.isLt)

end BipartiteDD.Haar.LiftA.{name}
"""


def check_module(spec, S):
    N, ns, bits, base, grp, mod = spec["N"], spec["ns"], spec["bits"], spec["base"], spec["grp"], spec["mod"]
    svec = ", ".join(f"⟨{a}, {j}⟩" for a, j in S)
    defs = []
    for cname, L, side in spec["covers"]:
        exps = exponents(side, L)
        expr = word_nested(L, exps) if cname == "D" else word_pairs(L, exps)
        defs.append(f"def word{cname} (c : ℕ) : Grp :=\n  {expr}\n")
    oks = [f"def ok{c} (c n : ℕ) : Bool := decide (grpOf n = word{c} c)\n" for c, _, _ in spec["covers"]]
    chks = [
        f"def chk{c} (base len C : ℕ) : Bool :=\n  (List.range len).all (fun i => ok{c} (codeAt C i) (base + i))\n"
        for c, _, _ in spec["covers"]
    ]
    exs = [
        f"""theorem stageEx{c} (base len C : ℕ) (h : chk{c} base len C = true) (n : ℕ) (hn : base ≤ n)
    (hn' : n < base + len) : ∃ c, ok{c} c n = true := by
  refine ⟨codeAt C (n - base), ?_⟩
  have := List.all_eq_true.mp h (n - base) (List.mem_range.mpr (by omega))
  rwa [show base + (n - base) = n by omega] at this
"""
        for c, _, _ in spec["covers"]
    ]
    return f"""import BipartiteDD.Haar.LiftA.{grp}

/-! Covering certificates of the lift record on {spec['nrec']} vertices: the Haar graph of `{grp}` with the connection
set `S` of `research/lifts/sols/{spec['sol']}` (degree {ns}).

For an index `n < {N}` the code `c` of a word holds {', '.join(str(L) for _, L, _ in spec['covers'])} base-{base} digits:
letter `i` of the word is `sel (digit c i)`, inverted or not as in the word definitions below. A stage table packs
`{N // spec['stages']}` codes of `{bits}` bits each. Generated by research/lean-haarD/gen_lift58410.py; do not edit by hand. -/

namespace BipartiteDD.Haar.LiftA.{mod}

open BipartiteDD.Haar.LiftA.{grp}

/-- The connection set `S`, as elements `(x, y)` of `{grp}`, in the order of the sol file. -/
def sVec : List Grp :=
  [{svec}]

/-- The `j`-th element of `S`. -/
def sel (j : ℕ) : Grp := sVec.getD j 1

/-- `S` as a finset. -/
def SS : Finset Grp := sVec.toFinset

theorem card_SS : SS.card = {ns} := by decide +kernel

theorem sel_mem_all : (List.range {ns}).all (fun j => decide (sel j ∈ SS)) = true := by
  decide +kernel

theorem sel_mem (j : ℕ) (hj : j < {ns}) : sel j ∈ SS := by
  have h := List.all_eq_true.mp sel_mem_all j (List.mem_range.mpr hj)
  simpa using h

/-- The digit `k` of the code `c`, in base {base}. -/
def digit (c k : ℕ) : ℕ := c / {base} ^ k % {base}

theorem digit_lt (c k : ℕ) : digit c k < {base} := Nat.mod_lt _ (by norm_num)

{chr(10).join(defs)}
{chr(10).join(oks)}
/-- A stage table is a natural number `C` holding codes of `{bits}` bits, the code `i` in bits
`[{bits} * i, {bits} * i + {bits})`. -/
def codeAt (C i : ℕ) : ℕ := (C >>> ({bits} * i)) % {2 ** bits}

{chr(10).join(chks)}
{chr(10).join(exs)}
end BipartiteDD.Haar.LiftA.{mod}
"""


def stage_module(spec, cname, idx, table):
    mod, grp, bits, size = spec["mod"], spec["grp"], spec["bits"], len(table)
    base = idx * size
    C = 0
    for i, code in enumerate(table):
        C |= code << (bits * i)
    st = f"stage{cname}{idx:02d}"
    ce = f"cert{cname}{idx:02d}"
    return f"""import BipartiteDD.Haar.LiftA.{mod}.Check

/-! Covering certificates, stage {idx:02d} of {spec['stages']} for the {cname} words: the indices `{base} ≤ n < {base + size}` of
the lift record on `{grp}`. `{st}` packs the codes of the elements with those indices: the code of index `{base} + i`
is `codeAt {st} i`. Generated by research/lean-haarD/gen_lift58410.py; do not edit by hand. -/

namespace BipartiteDD.Haar.LiftA.{mod}

def {st} : ℕ := {hexlit(C)}

set_option maxRecDepth 100000 in
theorem {ce} : chk{cname} {base} {size} {st} = true := by decide +kernel

end BipartiteDD.Haar.LiftA.{mod}
"""


def cover_module(spec):
    mod, grp, N, stages = spec["mod"], spec["grp"], spec["N"], spec["stages"]
    size = N // stages
    imports = [f"import BipartiteDD.Haar.LiftA.{mod}.Check"]
    for cname, _, _ in spec["covers"]:
        for s in range(stages):
            imports.append(f"import BipartiteDD.Haar.LiftA.{mod}.Stage{cname}{s:02d}")
    out = ["\n".join(imports), f"""
/-! Covering hypotheses of the lift record on `{grp}`: every element is a word of the required shape in `SS`, by the
kernel-checked certificates of the stage modules. Generated by research/lean-haarD/gen_lift58410.py; do not edit by
hand. -/

namespace BipartiteDD.Haar.LiftA.{mod}

open BipartiteDD.Haar.LiftA.{grp}
"""]
    for cname, _, _ in spec["covers"]:
        ks = " ∨ ".join(f"k = {s}" for s in range(stages))
        hs = " | ".join(f"h{s}" for s in range(stages))
        cases = "\n".join(
            f"  · exact stageEx{cname} {s * size} {size} stage{cname}{s:02d} cert{cname}{s:02d} n (by omega) (by omega)"
            for s in range(stages))
        out.append(f"""theorem ex{cname} (n : ℕ) (hn : n < {N}) : ∃ c, ok{cname} c n = true := by
  obtain ⟨k, hk⟩ : ∃ k, n / {size} = k := ⟨_, rfl⟩
  rcases (show {ks} by omega) with {hs}
{cases}
""")
    out.append(cover_statements(spec))
    out.append(f"end BipartiteDD.Haar.LiftA.{mod}\n")
    return "\n".join(out)


def cover_statements(spec):
    parts = []
    for cname, L, side in spec["covers"]:
        if cname == "A":
            parts.append("""theorem coverA (g : Grp) : ∃ a₁ ∈ SS, ∃ b₁ ∈ SS, ∃ a₂ ∈ SS, ∃ b₂ ∈ SS, ∃ a₃ ∈ SS, ∃ b₃ ∈ SS,
    ∃ a₄ ∈ SS, ∃ b₄ ∈ SS, g = a₁⁻¹ * b₁ * (a₂⁻¹ * b₂) * (a₃⁻¹ * b₃) * (a₄⁻¹ * b₄) := by
  obtain ⟨c, hc⟩ := exA (enc g) (enc_lt g)
  have h : grpOf (enc g) = wordA c := of_decide_eq_true hc
  rw [grpOf_enc] at h
  exact ⟨_, sel_mem _ (digit_lt c 0), _, sel_mem _ (digit_lt c 1), _, sel_mem _ (digit_lt c 2),
    _, sel_mem _ (digit_lt c 3), _, sel_mem _ (digit_lt c 4), _, sel_mem _ (digit_lt c 5),
    _, sel_mem _ (digit_lt c 6), _, sel_mem _ (digit_lt c 7), h⟩
""")
        elif cname == "B":
            parts.append("""theorem coverB (g : Grp) : ∃ a₁ ∈ SS, ∃ b₁ ∈ SS, ∃ a₂ ∈ SS, ∃ b₂ ∈ SS, ∃ a₃ ∈ SS, ∃ b₃ ∈ SS,
    ∃ a₄ ∈ SS, ∃ b₄ ∈ SS, g = a₁ * b₁⁻¹ * (a₂ * b₂⁻¹) * (a₃ * b₃⁻¹) * (a₄ * b₄⁻¹) := by
  obtain ⟨c, hc⟩ := exB (enc g) (enc_lt g)
  have h : grpOf (enc g) = wordB c := of_decide_eq_true hc
  rw [grpOf_enc] at h
  exact ⟨_, sel_mem _ (digit_lt c 0), _, sel_mem _ (digit_lt c 1), _, sel_mem _ (digit_lt c 2),
    _, sel_mem _ (digit_lt c 3), _, sel_mem _ (digit_lt c 4), _, sel_mem _ (digit_lt c 5),
    _, sel_mem _ (digit_lt c 6), _, sel_mem _ (digit_lt c 7), h⟩
""")
        elif cname == "C":
            parts.append("""theorem coverC (x : Grp) : ∃ s ∈ SS, ∃ a₁ ∈ SS, ∃ b₁ ∈ SS, ∃ a₂ ∈ SS, ∃ b₂ ∈ SS,
    ∃ a₃ ∈ SS, ∃ b₃ ∈ SS, x = a₁ * b₁⁻¹ * (a₂ * b₂⁻¹) * (a₃ * b₃⁻¹) * s := by
  obtain ⟨c, hc⟩ := exC (enc x) (enc_lt x)
  have h : grpOf (enc x) = wordC c := of_decide_eq_true hc
  rw [grpOf_enc] at h
  exact ⟨_, sel_mem _ (digit_lt c 6), _, sel_mem _ (digit_lt c 0), _, sel_mem _ (digit_lt c 1),
    _, sel_mem _ (digit_lt c 2), _, sel_mem _ (digit_lt c 3), _, sel_mem _ (digit_lt c 4),
    _, sel_mem _ (digit_lt c 5), h⟩
""")
        elif cname == "D":
            wit =", ".join(f"_, sel_mem _ (digit_lt c {i})" for i in range(L))
            parts.append(f"""theorem coverD (g : Grp) : ∃ x₁ ∈ SS, ∃ x₂ ∈ SS, ∃ x₃ ∈ SS, ∃ x₄ ∈ SS, ∃ x₅ ∈ SS,
    ∃ x₆ ∈ SS, ∃ x₇ ∈ SS, ∃ x₈ ∈ SS, ∃ x₉ ∈ SS,
    g = x₁ * (x₂⁻¹ * (x₃ * (x₄⁻¹ * (x₅ * (x₆⁻¹ * (x₇ * (x₈⁻¹ * x₉))))))) := by
  obtain ⟨c, hc⟩ := exD (enc g) (enc_lt g)
  have h : grpOf (enc g) = wordD c := of_decide_eq_true hc
  rw [grpOf_enc] at h
  exact ⟨{wit}, h⟩
""")
    return "\n".join(parts)


def record_module(spec):
    mod, grp, N, nrec, delta, D = spec["mod"], spec["grp"], spec["N"], spec["nrec"], spec["delta"], spec["D"]
    if D == 8:
        return f"""import BipartiteDD.Haar.LiftA.{mod}.Cover
import BipartiteDD.Haar.Diam8

/-! The ({delta},{D}) lift record on {nrec} vertices, the Haar graph of `{grp}` (order {N}) with the connection set of
`research/lifts/sols/{spec['sol']}`. The covering hypotheses are `coverA`, `coverB`, `coverC` of `{mod}.Cover`, and the
diameter-{D} lemma is `BipartiteDD.Haar.isBipartiteDegDiam8_of` (`Haar/Diam8.lean`). -/

namespace BipartiteDD.Haar.LiftA.{mod}

open BipartiteDD.Haar

/-- `({grp} ⊕ {grp}) ≃ Fin {nrec}`: the two sides, numbered `0 … {nrec - 1}`. -/
noncomputable def equiv{nrec} : {grp}.Grp ⊕ {grp}.Grp ≃ Fin {nrec} :=
  (Equiv.sumCongr {grp}.equivG {grp}.equivG).trans (finSumFinEquiv.trans (finCongr (by norm_num)))

/-- The Haar graph of `SS`, transported to `Fin {nrec}`. -/
noncomputable def G{nrec} : SimpleGraph (Fin {nrec}) := (haarGraph SS).comap equiv{nrec}.symm

theorem isBipartiteDegDiam_G{nrec} : BipartiteDD.IsBipartiteDegDiam G{nrec} {delta} {D} := by
  have h := isBipartiteDegDiam8_of SS G{nrec} equiv{nrec} (fun x y => by simp [G{nrec}, SimpleGraph.comap_adj])
    coverA coverB coverC
  rw [card_SS] at h
  exact h

end BipartiteDD.Haar.LiftA.{mod}

open BipartiteDD.Haar.LiftA.{mod} in
/-- A bipartite graph on {nrec} vertices with degree at most {delta} and diameter at most {D}. -/
theorem nb_{delta}_{D}_{nrec} : ∃ H : SimpleGraph (Fin {nrec}), BipartiteDD.IsBipartiteDegDiam H {delta} {D} :=
  ⟨G{nrec}, isBipartiteDegDiam_G{nrec}⟩
"""
    return f"""import BipartiteDD.Haar.LiftA.{mod}.Cover
import BipartiteDD.Haar.Diam10

/-! The ({delta},{D}) lift record on {nrec} vertices, the Haar graph of `{grp}` (order {N}) with the connection set of
`research/lifts/sols/{spec['sol']}`. The covering hypothesis is `coverD` of `{mod}.Cover`, and the diameter-{D} lemma is
`BipartiteDD.Haar.haar_isBipartiteDegDiam10_of_equiv` (`Haar/Diam10.lean`). -/

namespace BipartiteDD.Haar.LiftA.{mod}

open BipartiteDD.Haar

/-- `({grp} ⊕ {grp}) ≃ Fin {nrec}`: the two sides, numbered `0 … {nrec - 1}`. -/
noncomputable def equiv{nrec} : {grp}.Grp ⊕ {grp}.Grp ≃ Fin {nrec} :=
  (Equiv.sumCongr {grp}.equivG {grp}.equivG).trans (finSumFinEquiv.trans (finCongr (by norm_num)))

/-- The Haar graph of `SS`, transported to `Fin {nrec}`. -/
noncomputable def G{nrec} : SimpleGraph (Fin {nrec}) := (haarGraph SS).comap equiv{nrec}.symm

theorem isBipartiteDegDiam_G{nrec} : BipartiteDD.IsBipartiteDegDiam G{nrec} {delta} {D} := by
  have h := haar_isBipartiteDegDiam10_of_equiv SS equiv{nrec} coverD
  rw [card_SS] at h
  exact h

end BipartiteDD.Haar.LiftA.{mod}

open BipartiteDD.Haar.LiftA.{mod} in
/-- A bipartite graph on {nrec} vertices with degree at most {delta} and diameter at most {D}. -/
theorem nb_{delta}_{D}_{nrec} : ∃ H : SimpleGraph (Fin {nrec}), BipartiteDD.IsBipartiteDegDiam H {delta} {D} :=
  ⟨G{nrec}, isBipartiteDegDiam_G{nrec}⟩
"""


def main():
    out_root = sys.argv[1] if len(sys.argv) > 1 else os.path.join(REPO, "lean", "BipartiteDD", "Haar", "LiftA")
    for key, spec in RECORDS.items():
        mul, inv = group(spec["m"], spec["k"], spec["r"])
        S = parse_sol(os.path.join(SOLS, spec["sol"]), spec)
        print(key, "S =", S)
        spec["codes"] = {}
        for cname, L, side in spec["covers"]:
            codes = find_codes(mul, inv, S, spec, L, side)
            spec["codes"][cname] = codes
            print(" cover", cname, "letters", L, "entries", len(codes), "max code", max(codes),
                  "< base^L", spec["base"] ** L)
        d = os.path.join(out_root, spec["mod"])
        write(os.path.join(out_root, f"{spec['grp']}.lean"), meta_module(spec))
        write(os.path.join(d, "Check.lean"), check_module(spec, S))
        size = spec["N"] // spec["stages"]
        assert size * spec["stages"] == spec["N"]
        for cname, _, _ in spec["covers"]:
            codes = spec["codes"][cname]
            for s in range(spec["stages"]):
                write(os.path.join(d, f"Stage{cname}{s:02d}.lean"),
                      stage_module(spec, cname, s, codes[s * size:(s + 1) * size]))
        write(os.path.join(d, "Cover.lean"), cover_module(spec))
        write(os.path.join(d, "Record.lean"), record_module(spec))


if __name__ == "__main__":
    main()
