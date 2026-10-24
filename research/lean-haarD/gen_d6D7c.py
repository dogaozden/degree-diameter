#!/usr/bin/env python3
"""Covering certificates for the (6,7) Haar record on 8880 vertices: G = SL(2,5) x Z_37 (order 4440).

Numbering (must match lean/BipartiteDD/Haar/D6D7c/SL5.lean and SL5Z37.lean): the 120 elements of SL(2,5) are
numbered as in SL5.quad / SL5.enc: the 20 with c = 0 first, n = (a - 1) * 5 + b, then the 100 with c != 0,
n = 20 + ((c - 1) * 5 + a) * 5 + d, with b = (a d - 1) c^-1. The element (M, z) of G has index 37 * enc(M) + z.
Products are matrix products in SL(2,5) and sums mod 37 in the Z_37 factor.

S is read from the sol file (six elements (M, z), degree 6), research/frontier/sols/d6D7_sl_5_37_orb3f0_s2.txt.

Covering words. For every g in G there are two words of three pairs (digits d0..d5 in 0..5, indices into S):
  A-word: g = S[d0]^-1 S[d1] S[d2]^-1 S[d3] S[d4]^-1 S[d5]
  B-word: g = S[d0] S[d1]^-1 S[d2] S[d3]^-1 S[d4] S[d5]^-1
The code is sum_k d_k 6^k < 6^6 = 46656 < 2^16. Entry n of the A (resp. B) table is the code of the A (resp. B)
word of the element with index n. Every word is re-checked by direct multiplication.

Usage: python3 -I gen_d6D7c.py SOL.txt OUTDIR
writes OUTDIR/Check.lean, OUTDIR/Stage{00..04}.lean and OUTDIR/Cover.lean; OUTDIR is
lean/BipartiteDD/Haar/D6D7c/ (the Lean files are not produced anywhere else). The group files SL5.lean, SL5Z37.lean,
Record8880.lean and Axioms.lean there are written by hand.
"""
import itertools
import os
import re
import sys

P = 5          # SL(2, P)
Z = 37         # Z_Z factor
N = 120 * Z    # 4440
NS = 6
NPAIR = 3
STAGES = 5
STAGE = N // STAGES  # 888
BITS = 16
assert STAGE * STAGES == N
assert 6 ** (2 * NPAIR) < 2 ** BITS


# ---------------------------------------------------------------- SL(2,5) with the Lean numbering
def smul(A, B):
    a, b, c, d = A
    e, f, g, h = B
    return ((a * e + b * g) % P, (a * f + b * h) % P, (c * e + d * g) % P, (c * f + d * h) % P)


def sinv(A):
    a, b, c, d = A
    return (d % P, (-b) % P, (-c) % P, a % P)


def inv_p(x):
    return next(y for y in range(1, P) if x * y % P == 1)


def sl_quad(n):
    """Entries (a, b, c, d) of the element with index n in 0..119, as in SL5.quad."""
    if n < 20:
        a = n // 5 + 1
        b = n % 5
        return (a % P, b, 0, inv_p(a % P))
    m = n - 20
    a = m // 5 % 5
    c = m // 25 + 1
    d = m % 5
    b = (a * d - 1) * inv_p(c % P) % P
    return (a, b, c, d)


def sl_enc(A):
    a, b, c, d = A
    assert (a * d - b * c) % P == 1
    if c == 0:
        assert a != 0
        return (a - 1) * 5 + b
    return 20 + ((c - 1) * 5 + a) * 5 + d


def check_sl():
    seen = set()
    for n in range(120):
        A = sl_quad(n)
        assert (A[0] * A[3] - A[1] * A[2]) % P == 1, n
        assert sl_enc(A) == n, n
        seen.add(A)
    assert len(seen) == 120


# ---------------------------------------------------------------- G = SL(2,5) x Z_37
def mul(x, y):
    (A, z), (B, w) = x, y
    return (smul(A, B), (z + w) % Z)


def inv(x):
    A, z = x
    return (sinv(A), (-z) % Z)


def enc(x):
    A, z = x
    return sl_enc(A) * Z + z


def dec(n):
    return (sl_quad(n // Z), n % Z)


def parse_sol(path):
    lines = [ln.strip() for ln in open(path) if ln.strip()]
    head = lines[0].split()
    assert head[:2] == ["6", "7"] and head[2] == "sl" and head[3] == str(P) and head[5] == str(Z), head
    assert head[7] == str(N), head
    S = []
    for ln in lines[1:]:
        m = re.fullmatch(r"\d+\s+mat\((\d+),(\d+),(\d+),(\d+)\)\s+z=(\d+)", ln)
        assert m, ln
        a, b, c, d, z = map(int, m.groups())
        assert (a * d - b * c) % P == 1 and 0 <= z < Z, ln
        S.append(((a, b, c, d), z))
    assert len(S) == NS and len(set(S)) == NS, S
    return S


def check_group():
    for n in range(N):
        assert enc(dec(n)) == n
    for n in range(0, N, 37):
        x = dec(n)
        assert mul(x, inv(x)) == (((1, 0, 0, 1)), 0) and mul(inv(x), x) == (((1, 0, 0, 1)), 0), x
    # associativity on a sample
    xs = [dec(n) for n in (1, 50, 777, 4439)]
    for x in xs:
        for y in xs:
            for w in xs:
                assert mul(mul(x, y), w) == mul(x, mul(y, w))


def word_value(S, digs, side):
    el = ((1, 0, 0, 1), 0)
    for p in range(NPAIR):
        x, y = digs[2 * p], digs[2 * p + 1]
        if side == "A":
            el = mul(el, mul(inv(S[x]), S[y]))
        else:
            el = mul(el, mul(S[x], inv(S[y])))
    return el


def find_words(S):
    """For each index n, the A and B digit tuples (d0..d5) of a covering word."""
    results = {}
    for side in ("A", "B"):
        words = {}
        for digs in itertools.product(range(NS), repeat=2 * NPAIR):
            el = word_value(S, digs, side)
            words.setdefault(enc(el), digs)
        assert len(words) == N, (side, N - len(words))
        results[side] = [words[n] for n in range(N)]
    return results


def code_of(digs):
    return sum(d * 6 ** k for k, d in enumerate(digs))


def verify(S, digits):
    for side in ("A", "B"):
        for n in range(N):
            assert word_value(S, digits[side][n], side) == dec(n), (side, n)


CHECK = """import BipartiteDD.Haar.D6D7c.SL5Z37

/-! The covering certificates of the (6,7) Haar record on `SL(2, 5) × Z_37`, checked by kernel computation.

The connection set `S` is the six elements of `research/frontier/sols/d6D7_sl_5_37_orb3f0_s2.txt`. For each index
`n < 4440` a code `c` (a base-6 number with digits `d0 … d5`) gives two words:

  `wordA c = x1⁻¹ x2 x3⁻¹ x4 x5⁻¹ x6`  and  `wordB c = x1 x2⁻¹ x3 x4⁻¹ x5 x6⁻¹`,

with `xi = sel (d_{i-1})`. The predicates `okA c n`, `okB c n` say that the word is the element with index `n`.
The certificate tables are the stage modules `D6D7c.Stage00 … Stage04`, which are generated by
research/lean-haarD/gen_d6D7c.py. Each stage is checked by `decide +kernel`. -/

namespace BipartiteDD.Haar.D6D7c

open BipartiteDD.Haar.D6D7c.SL5Z37

/-- The connection set, as elements `(M, z)` of `SL(2, 5) × Z_37`, in the order of the sol file. -/
def sVec : List Grp :=
  [{svec}]

/-- The `j`-th element of `S`, for `j < 6`. -/
def sel (j : ℕ) : Grp := sVec.getD j 1

/-- `S` as a finset. -/
def SS : Finset Grp := sVec.toFinset

theorem card_SS : SS.card = 6 := by decide +kernel

theorem sel_mem_all : (List.range 6).all (fun j => decide (sel j ∈ SS)) = true := by
  decide +kernel

theorem sel_mem (j : ℕ) (hj : j < 6) : sel j ∈ SS := by
  have h := List.all_eq_true.mp sel_mem_all j (List.mem_range.mpr hj)
  simpa using h

/-- The digit `k` of the code `c`, in base 6. -/
def digit (c k : ℕ) : ℕ := c / 6 ^ k % 6

theorem digit_lt (c k : ℕ) : digit c k < 6 := Nat.mod_lt _ (by norm_num)

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

/-- A stage table is a natural number `C` holding `len` codes, `16` bits each, the code `i` in bits
`[16 i, 16 i + 16)`. Every code is below `6 ^ 6 = 46656 < 2 ^ 16`. -/
def codeAt (C i : ℕ) : ℕ := (C >>> (16 * i)) % 65536

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

end BipartiteDD.Haar.D6D7c
"""


LEAN_STAGE = """import BipartiteDD.Haar.D6D7c.Check

/-! Covering certificates, stage {k} of {stages}: the indices `{lo} ≤ n < {hi}` of the (6,7) record on
`SL(2, 5) × Z_37`. Generated by research/lean-haarD/gen_d6D7c.py. Do not edit by hand.

`stageA{k}` (resp. `stageB{k}`) packs the base-6 codes of the A-words (resp. B-words) of the elements with indices
`{lo} ≤ n < {hi}`: the code of index `{lo} + i` is `codeAt stageA{k} i`, 16 bits each. -/

namespace BipartiteDD.Haar.D6D7c

def stageA{k} : ℕ := {a}

def stageB{k} : ℕ := {b}

set_option maxRecDepth 100000 in
theorem certA{k} : chkA {lo} {len} stageA{k} = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem certB{k} : chkB {lo} {len} stageB{k} = true := by decide +kernel

end BipartiteDD.Haar.D6D7c
"""

COVER = """import BipartiteDD.Haar.D6D7c.Check
{imports}

/-! Covering hypotheses of the (6,7) record: every element of `SL(2, 5) × Z_37` is an A-word and a B-word in
the connection set `SS`, by the kernel-checked certificates of the stage modules. Generated by
research/lean-haarD/gen_d6D7c.py. Do not edit by hand. -/

namespace BipartiteDD.Haar.D6D7c

open BipartiteDD.Haar.D6D7c.SL5Z37

/-- Every index `n < 4440` has an A-code. -/
theorem exA (n : ℕ) (hn : n < 4440) : ∃ c, okA c n = true := by
  obtain ⟨k, hk⟩ : ∃ k, n / {stage} = k := ⟨_, rfl⟩
  have hk12 : k < {stages} := by omega
  rcases (show {ors} by omega) with {alts}
{casesA}

/-- Every index `n < 4440` has a B-code. -/
theorem exB (n : ℕ) (hn : n < 4440) : ∃ c, okB c n = true := by
  obtain ⟨k, hk⟩ : ∃ k, n / {stage} = k := ⟨_, rfl⟩
  have hk12 : k < {stages} := by omega
  rcases (show {ors} by omega) with {alts}
{casesB}

theorem cover1 : ∀ g : Grp, ∃ x1 ∈ SS, ∃ x2 ∈ SS, ∃ x3 ∈ SS, ∃ x4 ∈ SS, ∃ x5 ∈ SS, ∃ x6 ∈ SS,
    g = x1⁻¹ * x2 * x3⁻¹ * x4 * x5⁻¹ * x6 := by
  intro g
  obtain ⟨c, hc⟩ := exA (enc g) (enc_lt g)
  have h : grpOf (enc g) = wordA c := of_decide_eq_true hc
  rw [grpOf_enc] at h
  exact ⟨_, sel_mem _ (digit_lt c 0), _, sel_mem _ (digit_lt c 1), _, sel_mem _ (digit_lt c 2),
    _, sel_mem _ (digit_lt c 3), _, sel_mem _ (digit_lt c 4), _, sel_mem _ (digit_lt c 5), h⟩

theorem cover2 : ∀ g : Grp, ∃ x1 ∈ SS, ∃ x2 ∈ SS, ∃ x3 ∈ SS, ∃ x4 ∈ SS, ∃ x5 ∈ SS, ∃ x6 ∈ SS,
    g = x1 * x2⁻¹ * x3 * x4⁻¹ * x5 * x6⁻¹ := by
  intro g
  obtain ⟨c, hc⟩ := exB (enc g) (enc_lt g)
  have h : grpOf (enc g) = wordB c := of_decide_eq_true hc
  rw [grpOf_enc] at h
  exact ⟨_, sel_mem _ (digit_lt c 0), _, sel_mem _ (digit_lt c 1), _, sel_mem _ (digit_lt c 2),
    _, sel_mem _ (digit_lt c 3), _, sel_mem _ (digit_lt c 4), _, sel_mem _ (digit_lt c 5), h⟩

end BipartiteDD.Haar.D6D7c
"""


def cover_text():
    imports = "\n".join("import BipartiteDD.Haar.D6D7c.Stage%02d" % k for k in range(STAGES))
    cases = {}
    for side in ("A", "B"):
        lines = []
        for k in range(STAGES):
            lines.append("  · exact stageEx%s %d %d stage%s%02d cert%s%02d n (by omega) (by omega)"
                         % (side, k * STAGE, STAGE, side, k, side, k))
        cases[side] = "\n".join(lines)
    text = COVER
    text = text.replace("{imports}", imports)
    text = text.replace("{stage}", str(STAGE))
    text = text.replace("{stages}", str(STAGES))
    ors = " ∨ ".join("k = %d" % k for k in range(STAGES))
    alts = " | ".join("h%d" % k for k in range(STAGES))
    text = text.replace("{ors}", "(" + ors + ")").replace("{alts}", alts)
    text = text.replace("{casesA}", cases["A"])
    text = text.replace("{casesB}", cases["B"])
    return text


def check_text(S):
    svec = ", ".join("(⟨%d, %d, %d, %d, by decide⟩, Multiplicative.ofAdd ((%d : ℕ) : ZMod 37))"
                     % (a, b, c, d, z) for ((a, b, c, d), z) in S)
    return CHECK.replace("{svec}", svec)


def pack(codes):
    v = 0
    for i, c in enumerate(codes):
        assert 0 <= c < 2 ** BITS
        v |= c << (BITS * i)
    return v


def emit_lean(S, digits, outdir):
    os.makedirs(outdir, exist_ok=True)
    with open(os.path.join(outdir, "Check.lean"), "w") as f:
        f.write(check_text(S))
    for k in range(STAGES):
        lo = k * STAGE
        hi = lo + STAGE
        ca = [code_of(digits["A"][n]) for n in range(lo, hi)]
        cb = [code_of(digits["B"][n]) for n in range(lo, hi)]
        text = LEAN_STAGE.format(k="%02d" % k, stages=STAGES, lo=lo, hi=hi, len=STAGE,
                                 a="0x%x" % pack(ca), b="0x%x" % pack(cb))
        with open(os.path.join(outdir, "Stage%02d.lean" % k), "w") as f:
            f.write(text)
    with open(os.path.join(outdir, "Cover.lean"), "w") as f:
        f.write(cover_text())


def main():
    sol, outdir = sys.argv[1], sys.argv[2]
    S = parse_sol(sol)
    check_sl()
    check_group()
    digits = find_words(S)
    verify(S, digits)
    emit_lean(S, digits, outdir)
    print("S =", S)
    print("verified A and B words for all", N, "elements")


if __name__ == "__main__":
    main()
