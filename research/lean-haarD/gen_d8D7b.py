#!/usr/bin/env python3
"""Covering certificates for the (8,7) Haar record 43344: G = SL(2,8) x Z_43 (order 21672), S from
research/frontier/sols/d8D7_sl_8_43_orb3_s1.txt (8 elements). The Haar graph has 2 * 21672 = 43344 vertices.

Field: GF(8) = GF(2)[x]/(x^3+x+1). An element is a number 0..7, bit i the coefficient of x^i; addition is xor.
The product is the product of polynomials reduced by x^3 = x+1, computed as `mulN` in
lean/BipartiteDD/Haar/D8D7b/GF8.lean. The solution header must say `sl 8 poly x^3+x+1`.

Numbering (must match lean/BipartiteDD/Haar/D8D7b/SL8.lean and SL8Z43.lean):
  SL(2,8) element [[a,b],[c,d]] has index enc(a,b,c,d) in [0, 504):
    c = 0:  (a-1)*8 + b                        (a in 1..7, b in 0..7; 56 elements, d = a^-1)
    c != 0: 56 + ((c-1)*8 + a)*8 + d           (c in 1..7, a, d in 0..7; 448 elements, b = (ad+1)/c)
  G element (M, z) has index n = 43*enc(M) + z.

Certificates. For every g in G, two words of three pairs (digits d0..d5 in 0..7, indices into S):
  A-word: g = P(d0,d1) P(d2,d3) P(d4,d5),   P(x,y) = s_x^-1 s_y
  B-word: g = Q(d0,d1) Q(d2,d3) Q(d4,d5),   Q(x,y) = s_x s_y^-1
Three pairs give walks of length 6 on each side, so the diameter is 2*3 + 1 = 7 (haar_ediam_le_odd with n = 3).
The code is sum_k d_k 8^k (< 8^6 = 2^18). Entry n of the A (resp. B) table is the code of the A (resp. B) word
of the element with index n. Every word is re-checked here by direct multiplication.

Usage: python3 gen_d8D7b.py SOL.txt OUTDIR
writes OUTDIR/Stage{00..11}.lean, OUTDIR/Cover.lean and OUTDIR/Check.lean (OUTDIR is a scratch directory).
Copy them into lean/BipartiteDD/Haar/D8D7b/ by hand, next to the hand-written GF8.lean, SL8.lean and SL8Z43.lean.
"""
import os
import re
import sys

import numpy as np

Q2 = 8  # |GF(8)|
NZ = 43
NSL = 504  # |SL(2,8)| = 8 * (8^2 - 1)
N = NSL * NZ  # 21672
NS = 8
DIGITS = 6
BASE = 8
CODE_BITS = 18  # 8^6 = 2^18
STAGES = 12
STAGE = N // STAGES  # 1806
assert STAGE * STAGES == N
C0 = (Q2 - 1) * Q2  # 56: elements with c = 0


def mul8(a, b):
    """Product in GF(8), as `mulN` in GF8.lean."""
    m = (a if b & 1 else 0) ^ ((a << 1) if b & 2 else 0) ^ ((a << 2) if b & 4 else 0)
    if m & 16:
        m ^= 22
    if m & 8:
        m ^= 11
    return m


def mul8_poly(a, b):
    """Independent check: polynomial product over GF(2), reduced modulo x^3 + x + 1."""
    p = 0
    for i in range(3):
        if (b >> i) & 1:
            p ^= a << i
    for k in (4, 3):
        if (p >> k) & 1:
            p ^= 0b1011 << (k - 3)
    return p


assert all(mul8(a, b) == mul8_poly(a, b) for a in range(8) for b in range(8))
MUL = np.array([[mul8(a, b) for b in range(8)] for a in range(8)], dtype=np.int64)
INV = [0] + [next(b for b in range(1, 8) if mul8(a, b) == 1) for a in range(1, 8)]
assert all(mul8(a, INV[a]) == 1 for a in range(1, 8))


def enc_sl(a, b, c, d):
    if c == 0:
        return (a - 1) * Q2 + b
    return C0 + ((c - 1) * Q2 + a) * Q2 + d


def quad_sl(m):
    if m < C0:
        a = m // Q2 + 1
        return (a, m % Q2, 0, INV[a])
    mm = m - C0
    c = mm // (Q2 * Q2) + 1
    a = (mm // Q2) % Q2
    d = mm % Q2
    b = mul8(mul8(a, d) ^ 1, INV[c])  # b c = a d + 1 (char 2)
    return (a, b, c, d)


def enc_g(a, b, c, d, z):
    return NZ * enc_sl(a, b, c, d) + z


def quad_g(n):
    a, b, c, d = quad_sl(n // NZ)
    return (a, b, c, d, n % NZ)


def mul(x, y):
    a, b, c, d, z = x
    e, f, g, h, w = y
    return (mul8(a, e) ^ mul8(b, g), mul8(a, f) ^ mul8(b, h),
            mul8(c, e) ^ mul8(d, g), mul8(c, f) ^ mul8(d, h), (z + w) % NZ)


def inv(x):
    """The inverse of a determinant-1 element: [[d, b], [c, a]] (char 2), z negated."""
    a, b, c, d, z = x
    return (d, b, c, a, (-z) % NZ)


def one():
    return (1, 0, 0, 1, 0)


def parse_sol(path):
    lines = [ln.strip() for ln in open(path) if ln.strip()]
    head = lines[0].split()
    assert head[0] == "8" and head[1] == "7" and head[2] == "sl" and int(head[3]) == Q2, head
    assert head[4] == "poly" and head[5] == "x^3+x+1", head
    assert head[6] == "n" and int(head[7]) == NZ and head[8] == "N" and int(head[9]) == N, head
    S = []
    for ln in lines[1:]:
        m = re.fullmatch(r"\d+\s+mat\((\d+),(\d+),(\d+),(\d+)\)\s+z=(\d+)", ln)
        assert m, ln
        a, b, c, d, z = map(int, m.groups())
        assert mul8(a, d) ^ mul8(b, c) == 1, ln
        S.append((a, b, c, d, z))
    assert len(S) == NS and len(set(S)) == NS, S
    return S


def check_group_numbering():
    seen = set()
    for n in range(N):
        g = quad_g(n)
        a, b, c, d, z = g
        assert mul8(a, d) ^ mul8(b, c) == 1, (n, g)
        assert enc_g(a, b, c, d, z) == n, (n, g)
        seen.add(g)
    assert len(seen) == N


def find_words(S):
    """For each index n, the A and B digit tuples (d0..d5) of its covering words."""
    Sinv = [inv(s) for s in S]
    PA = {}
    PB = {}
    for x in range(NS):
        for y in range(NS):
            PA[(x, y)] = mul(Sinv[x], S[y])
            PB[(x, y)] = mul(S[x], Sinv[y])

    allg = [quad_g(n) for n in range(N)]
    A = np.array([g[0] for g in allg], dtype=np.int64)
    B = np.array([g[1] for g in allg], dtype=np.int64)
    C = np.array([g[2] for g in allg], dtype=np.int64)
    D = np.array([g[3] for g in allg], dtype=np.int64)
    Z = np.array([g[4] for g in allg], dtype=np.int64)

    results = {}
    for side, P in (("A", PA), ("B", PB)):
        # two-pair products, indexed by element
        table = {}
        for (x1, y1), p1 in P.items():
            for (x2, y2), p2 in P.items():
                table.setdefault(enc_g(*mul(p1, p2)), (x1, y1, x2, y2))
        mask = np.zeros(N, dtype=bool)
        mask[list(table.keys())] = True
        # one-pair products Y; then g = X Y with X = g Y^-1 in the table
        ylist = {}
        for (x3, y3) in P:
            yel = P[(x3, y3)]
            ylist.setdefault(enc_g(*yel), (yel, (x3, y3)))
        words = {}
        for _, (yel, ydig) in ylist.items():
            ya, yb, yc, yd, yz = inv(yel)
            Xa = MUL[A, ya] ^ MUL[B, yc]
            Xb = MUL[A, yb] ^ MUL[B, yd]
            Xc = MUL[C, ya] ^ MUL[D, yc]
            Xd = MUL[C, yb] ^ MUL[D, yd]
            Xz = (Z + yz) % NZ
            Xn = NZ * np.where(Xc == 0, (Xa - 1) * Q2 + Xb, C0 + ((Xc - 1) * Q2 + Xa) * Q2 + Xd) + Xz
            hit = mask[Xn]
            for n in np.nonzero(hit)[0]:
                n = int(n)
                if n not in words:
                    words[n] = list(table[int(Xn[n])]) + list(ydig)
        assert len(words) == N, (side, N - len(words))
        results[side] = [words[n] for n in range(N)]
    return results


def word_value(S, digs, side):
    el = one()
    for k in range(0, DIGITS, 2):
        x, y = digs[k], digs[k + 1]
        if side == "A":
            el = mul(el, mul(inv(S[x]), S[y]))
        else:
            el = mul(el, mul(S[x], inv(S[y])))
    return el


def code_of(digs):
    return sum(d * BASE ** k for k, d in enumerate(digs))


def verify(S, digits):
    for side in ("A", "B"):
        for n in range(N):
            assert len(digits[side][n]) == DIGITS
            assert word_value(S, digits[side][n], side) == quad_g(n), (side, n)


LEAN_STAGE = """import BipartiteDD.Haar.D8D7b.Check

/-! Covering certificates, stage {k} of {stages}: the indices `{lo} ≤ n < {hi}` of the (8,7) record 43344 on
`SL(2, 8) × Z_43`. Generated by research/lean-haarD/gen_d8D7b.py. Do not edit by hand.

`stageA{k}` (resp. `stageB{k}`) packs the base-8 codes of the A-words (resp. B-words) of the elements with indices
`{lo} ≤ n < {hi}`: the code of index `{lo} + i` is `codeAt stageA{k} i`, 18 bits each. -/

namespace BipartiteDD.Haar.D8D7b

def stageA{k} : ℕ := {a}

def stageB{k} : ℕ := {b}

set_option maxRecDepth 100000 in
theorem certA{k} : chkA {lo} {len} stageA{k} = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem certB{k} : chkB {lo} {len} stageB{k} = true := by decide +kernel

end BipartiteDD.Haar.D8D7b
"""


def write_stages(outdir, digits):
    for k in range(STAGES):
        lo = k * STAGE
        tabs = {}
        for side in ("A", "B"):
            C = 0
            for i in range(STAGE):
                C |= code_of(digits[side][lo + i]) << (CODE_BITS * i)
            tabs[side] = hex(C)
        text = LEAN_STAGE.format(k=f"{k:02d}", stages=STAGES, lo=lo, hi=lo + STAGE, len=STAGE,
                                 a=tabs["A"], b=tabs["B"])
        with open(os.path.join(outdir, f"Stage{k:02d}.lean"), "w") as f:
            f.write(text)


def write_cover(outdir):
    cases_or = " ∨ ".join(f"k = {k}" for k in range(STAGES))
    rcases = " | ".join(f"h{k}" for k in range(STAGES))
    out = [
        "import BipartiteDD.Haar.D8D7b.Check",
    ]
    out += [f"import BipartiteDD.Haar.D8D7b.Stage{k:02d}" for k in range(STAGES)]
    out += [
        "",
        "/-! Covering hypotheses of the (8,7) record 43344: every element of `SL(2, 8) × Z_43` is an A-word and a",
        "B-word in the connection set `SS`, by the kernel-checked certificates of the stage modules. Generated by",
        "research/lean-haarD/gen_d8D7b.py. Do not edit by hand. -/",
        "",
        "namespace BipartiteDD.Haar.D8D7b",
        "",
        "open BipartiteDD.Haar.SL8Z43",
        "",
    ]
    for side in ("A", "B"):
        out.append(f"/-- Every index `n < {N}` has a {side}-code. -/")
        out.append(f"theorem ex{side} (n : ℕ) (hn : n < {N}) : ∃ c, ok{side} c n = true := by")
        out.append(f"  obtain ⟨k, hk⟩ : ∃ k, n / {STAGE} = k := ⟨_, rfl⟩")
        out.append(f"  have hk12 : k < {STAGES} := by omega")
        out.append(f"  rcases (show {cases_or} by omega) with {rcases}")
        for k in range(STAGES):
            lo = k * STAGE
            out.append(f"  · exact stageEx{side} {lo} {STAGE} stage{side}{k:02d} cert{side}{k:02d} n "
                       f"(by omega) (by omega)")
        out.append("")
    out += [
        "theorem cover1 : ∀ g : Grp, ∃ x1 ∈ SS, ∃ x2 ∈ SS, ∃ x3 ∈ SS, ∃ x4 ∈ SS, ∃ x5 ∈ SS, ∃ x6 ∈ SS,",
        "    g = x1⁻¹ * x2 * x3⁻¹ * x4 * x5⁻¹ * x6 := by",
        "  intro g",
        "  obtain ⟨c, hc⟩ := exA (enc g) (enc_lt g)",
        "  have h : grpOf (enc g) = wordA c := of_decide_eq_true hc",
        "  rw [grpOf_enc] at h",
        "  exact ⟨_, sel_mem _ (digit_lt c 0), _, sel_mem _ (digit_lt c 1), _, sel_mem _ (digit_lt c 2),",
        "    _, sel_mem _ (digit_lt c 3), _, sel_mem _ (digit_lt c 4), _, sel_mem _ (digit_lt c 5), h⟩",
        "",
        "theorem cover2 : ∀ g : Grp, ∃ x1 ∈ SS, ∃ x2 ∈ SS, ∃ x3 ∈ SS, ∃ x4 ∈ SS, ∃ x5 ∈ SS, ∃ x6 ∈ SS,",
        "    g = x1 * x2⁻¹ * x3 * x4⁻¹ * x5 * x6⁻¹ := by",
        "  intro g",
        "  obtain ⟨c, hc⟩ := exB (enc g) (enc_lt g)",
        "  have h : grpOf (enc g) = wordB c := of_decide_eq_true hc",
        "  rw [grpOf_enc] at h",
        "  exact ⟨_, sel_mem _ (digit_lt c 0), _, sel_mem _ (digit_lt c 1), _, sel_mem _ (digit_lt c 2),",
        "    _, sel_mem _ (digit_lt c 3), _, sel_mem _ (digit_lt c 4), _, sel_mem _ (digit_lt c 5), h⟩",
        "",
        "end BipartiteDD.Haar.D8D7b",
        "",
    ]
    with open(os.path.join(outdir, "Cover.lean"), "w") as f:
        f.write("\n".join(out))


CHECK_HEAD = """import BipartiteDD.Haar.D8D7b.SL8Z43

/-! The covering certificates of the (8,7) Haar record 43344 on `SL(2, 8) × Z_43`, checked by kernel computation.

The connection set `S` is the eight elements of `research/frontier/sols/d8D7_sl_8_43_orb3_s1.txt`. For each index
`n < 21672` a code `c` (a base-8 number with digits `d0 … d5`) gives two words:

  `wordA c = x1⁻¹ x2 x3⁻¹ x4 x5⁻¹ x6`  and  `wordB c = x1 x2⁻¹ x3 x4⁻¹ x5 x6⁻¹`,

with `xi = sel (d_{i-1})`. The predicates `okA c n`, `okB c n` say that the word is the element with index `n`.
The certificate tables are the stage modules `D8D7b.Stage00 … Stage11`, which are generated by
research/lean-haarD/gen_d8D7b.py. Each stage is checked by `decide +kernel`. -/

namespace BipartiteDD.Haar.D8D7b

open BipartiteDD.Haar.D8D7b.SL8Z43

/-- The connection set, as elements `(M, z)` of `SL(2,8) × Z_43`. -/
def sVec : List Grp :=
"""

CHECK_TAIL = """
/-- The `j`-th element of `S`, for `j < 8`. -/
def sel (j : ℕ) : Grp := sVec.getD j 1

/-- `S` as a finset. -/
def SS : Finset Grp := sVec.toFinset

theorem card_SS : SS.card = 8 := by decide +kernel

theorem sel_mem_all : (List.range 8).all (fun j => decide (sel j ∈ SS)) = true := by
  decide +kernel

theorem sel_mem (j : ℕ) (hj : j < 8) : sel j ∈ SS := by
  have h := List.all_eq_true.mp sel_mem_all j (List.mem_range.mpr hj)
  simpa using h

/-- The digit `k` of the code `c`, in base 8. -/
def digit (c k : ℕ) : ℕ := c / 8 ^ k % 8

theorem digit_lt (c k : ℕ) : digit c k < 8 := Nat.mod_lt _ (by decide)

/-- The A-word of the code `c`: `x1⁻¹ x2 x3⁻¹ x4 x5⁻¹ x6`. -/
def wordA (c : ℕ) : Grp :=
  (sel (digit c 0))⁻¹ * sel (digit c 1) * (sel (digit c 2))⁻¹ * sel (digit c 3) *
    (sel (digit c 4))⁻¹ * sel (digit c 5)

/-- The B-word of the code `c`: `x1 x2⁻¹ x3 x4⁻¹ x5 x6⁻¹`. -/
def wordB (c : ℕ) : Grp :=
  sel (digit c 0) * (sel (digit c 1))⁻¹ * sel (digit c 2) * (sel (digit c 3))⁻¹ *
    sel (digit c 4) * (sel (digit c 5))⁻¹

/-- The code `c` gives the A-word of the element with index `n`. -/
def okA (c n : ℕ) : Bool := decide (grpOf n = wordA c)

/-- The code `c` gives the B-word of the element with index `n`. -/
def okB (c n : ℕ) : Bool := decide (grpOf n = wordB c)

/-- A stage table is a natural number `C` holding `len` codes, `18` bits each, the code `i` in bits
`[18 i, 18 i + 18)`. Every code is below `8 ^ 6 = 2 ^ 18`. -/
def codeAt (C i : ℕ) : ℕ := (C >>> (18 * i)) % 262144

/-- `chkA base len C` checks that the code `i` of the table `C` is an A-code for the index `base + i`,
for `i < len`. -/
def chkA (base len C : ℕ) : Bool :=
  (List.range len).all (fun i => okA (codeAt C i) (base + i))

/-- `chkB base len C` checks that the code `i` of the table `C` is a B-code for the index `base + i`,
for `i < len`. -/
def chkB (base len C : ℕ) : Bool :=
  (List.range len).all (fun i => okB (codeAt C i) (base + i))

/-- An index `n` in the stage `[base, base + len)` has an A-code, given the stage check. -/
theorem stageExA (base len C : ℕ) (h : chkA base len C = true) (n : ℕ) (hn : base ≤ n)
    (hn' : n < base + len) : ∃ c, okA c n = true := by
  refine ⟨codeAt C (n - base), ?_⟩
  have := List.all_eq_true.mp h (n - base) (List.mem_range.mpr (by omega))
  rwa [show base + (n - base) = n by omega] at this

/-- An index `n` in the stage `[base, base + len)` has a B-code, given the stage check. -/
theorem stageExB (base len C : ℕ) (h : chkB base len C = true) (n : ℕ) (hn : base ≤ n)
    (hn' : n < base + len) : ∃ c, okB c n = true := by
  refine ⟨codeAt C (n - base), ?_⟩
  have := List.all_eq_true.mp h (n - base) (List.mem_range.mpr (by omega))
  rwa [show base + (n - base) = n by omega] at this

end BipartiteDD.Haar.D8D7b
"""


def write_check(outdir, S):
    elems = []
    for a, b, c, d, z in S:
        elems.append(f"(⟨ofN {a}, ofN {b}, ofN {c}, ofN {d}, by decide⟩, Multiplicative.ofAdd ({z} : ZMod {NZ}))")
    body = "  [" + ",\n    ".join(elems) + "]\n"
    with open(os.path.join(outdir, "Check.lean"), "w") as f:
        f.write(CHECK_HEAD + body + CHECK_TAIL)


def main():
    sol, outdir = sys.argv[1], sys.argv[2]
    os.makedirs(outdir, exist_ok=True)
    S = parse_sol(sol)
    check_group_numbering()
    digits = find_words(S)
    verify(S, digits)
    write_stages(outdir, digits)
    write_cover(outdir)
    write_check(outdir, S)
    print("verified: all", N, "elements have A- and B-words of length 6 in S")


if __name__ == "__main__":
    main()
