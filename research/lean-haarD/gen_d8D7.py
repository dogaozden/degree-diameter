#!/usr/bin/env python3
"""Covering certificates for the (8,7) Haar record: G = SL(2,19) x Z_3 (order 20520), S from
research/frontier/sols/d8D7_sl_19_3_s2.txt (8 elements). The Haar graph has 41040 vertices.

Numbering (must match lean/BipartiteDD/Haar/SL19.lean and SL19Z3.lean):
  SL(2,19) element [[a,b],[c,d]] has index enc(a,b,c,d) in [0, 6840):
    c = 0:  (a-1)*19 + b                      (a in 1..18, b in 0..18; 342 elements)
    c != 0: 342 + ((c-1)*19 + a)*19 + d        (c in 1..18; 6498 elements)
  G element (M, z) has index n = 3*enc(M) + z.

Certificates. For every g in G, two words of three pairs (digits d0..d5 in 0..7, indices into S):
  A-word: g = P(d0,d1) P(d2,d3) P(d4,d5),   P(x,y) = s_x^-1 s_y
  B-word: g = Q(d0,d1) Q(d2,d3) Q(d4,d5),   Q(x,y) = s_x s_y^-1
Three pairs give walks of length 6 on each side, so the diameter is 2*3 + 1 = 7 (haar_ediam_le_odd with n = 3).
The code is sum_k d_k 8^k (< 8^6 = 2^18). Entry n of the A (resp. B) table is the code of the A (resp. B) word
of the element with index n. Every word is re-checked here by direct multiplication.

Usage: python3 gen_d8D7.py SOL.txt OUTDIR
writes OUTDIR/codes.json, OUTDIR/lean/Stage{00..11}.lean, OUTDIR/lean/Cover.lean, OUTDIR/lean/Check.lean.
The Lean files are copied to lean/BipartiteDD/Haar/D8D7/ by hand (the generator does not touch the repo).
"""
import json
import os
import re
import sys

import numpy as np

Q = 19
NZ = 3
NSL = Q * (Q * Q - 1)  # 6840
N = NSL * NZ  # 20520
NS = 8
NPAIR = 3  # pairs per word: 6 letters
DIGITS = 2 * NPAIR  # 6
BASE = NS  # digits are in 0..7
CODE_BITS = 18  # 8^6 = 2^18
STAGES = 12
STAGE = N // STAGES  # 1710
assert STAGE * STAGES == N
C0 = (Q - 1) * Q  # 342: number of SL(2,19) elements with c = 0
assert NSL - C0 == 6498


def inv_mod(x):
    return pow(int(x), Q - 2, Q)


def enc_sl(a, b, c, d):
    if c == 0:
        return (a - 1) * Q + b
    return C0 + ((c - 1) * Q + a) * Q + d


def quad_sl(m):
    if m < C0:
        a = m // Q + 1
        return (a, m % Q, 0, inv_mod(a))
    mm = m - C0
    a = (mm // Q) % Q
    c = mm // (Q * Q) + 1
    d = mm % Q
    b = ((a * d - 1) * inv_mod(c)) % Q
    return (a, b, c, d)


def enc_g(a, b, c, d, z):
    return NZ * enc_sl(a, b, c, d) + z


def quad_g(n):
    a, b, c, d = quad_sl(n // NZ)
    return (a, b, c, d, n % NZ)


def mul(x, y):
    a, b, c, d, z = x
    e, f, g, h, w = y
    return ((a * e + b * g) % Q, (a * f + b * h) % Q, (c * e + d * g) % Q, (c * f + d * h) % Q, (z + w) % NZ)


def inv(x):
    a, b, c, d, z = x
    return (d % Q, (-b) % Q, (-c) % Q, a % Q, (-z) % NZ)


def one():
    return (1, 0, 0, 1, 0)


def parse_sol(path):
    lines = [ln.strip() for ln in open(path) if ln.strip()]
    head = lines[0].split()
    assert head[0] == "8" and head[1] == "7" and head[2] == "sl" and int(head[3]) == Q, head
    assert int(head[5]) == NZ and int(head[7]) == N, head
    S = []
    for ln in lines[1:]:
        m = re.fullmatch(r"\d+\s+mat\((\d+),(\d+),(\d+),(\d+)\)\s+z=(\d+)", ln)
        assert m, ln
        a, b, c, d, z = map(int, m.groups())
        assert (a * d - b * c) % Q == 1, ln
        S.append((a, b, c, d, z))
    assert len(S) == NS and len(set(S)) == NS, S
    return S


def check_group_numbering():
    seen = set()
    for n in range(N):
        g = quad_g(n)
        a, b, c, d, z = g
        assert (a * d - b * c) % Q == 1, (n, g)
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
        # left part: two-pair products X (four digits), indexed by element
        table = {}
        for (x1, y1), p1 in P.items():
            for (x2, y2), p2 in P.items():
                table.setdefault(enc_g(*mul(p1, p2)), (x1, y1, x2, y2))
        mask = np.zeros(N, dtype=bool)
        mask[list(table.keys())] = True
        # right part: one-pair products Y (two digits); then g = X Y with X = g Y^-1 in the table
        ylist = {}
        for (x3, y3) in P:
            yel = P[(x3, y3)]
            ylist.setdefault(enc_g(*yel), (yel, (x3, y3)))
        words = {}
        for _, (yel, ydig) in ylist.items():
            ya, yb, yc, yd, yz = inv(yel)
            Xa = (A * ya + B * yc) % Q
            Xb = (A * yb + B * yd) % Q
            Xc = (C * ya + D * yc) % Q
            Xd = (C * yb + D * yd) % Q
            Xz = (Z + yz) % NZ
            Xn = NZ * np.where(Xc == 0, (Xa - 1) * Q + Xb, C0 + ((Xc - 1) * Q + Xa) * Q + Xd) + Xz
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


LEAN_STAGE = """import BipartiteDD.Haar.D8D7.Check

/-! Covering certificates, stage {k} of {stages}: the indices `{lo} ≤ n < {hi}` of the (8,7) record on
`SL(2, 19) × Z_3`. Generated by research/lean-haarD/gen_d8D7.py. Do not edit by hand.

`stageA{k}` (resp. `stageB{k}`) packs the base-8 codes of the A-words (resp. B-words) of the elements with indices
`{lo} ≤ n < {hi}`: the code of index `{lo} + i` is `codeAt stageA{k} i`, 18 bits each. -/

namespace BipartiteDD.Haar.D8D7

def stageA{k} : ℕ := {a}

def stageB{k} : ℕ := {b}

set_option maxRecDepth 100000 in
theorem certA{k} : chkA {lo} {len} stageA{k} = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem certB{k} : chkB {lo} {len} stageB{k} = true := by decide +kernel

end BipartiteDD.Haar.D8D7
"""

CHECK = """import BipartiteDD.Haar.SL19Z3

/-! The covering certificates of the (8,7) Haar record on `SL(2, 19) × Z_3`, checked by kernel computation.

The connection set `S` is the eight elements of `research/frontier/sols/d8D7_sl_19_3_s2.txt`. For each index
`n < 20520` a code `c` (a base-8 number with digits `d0 … d5`) gives two words:

  `wordA c = x1⁻¹ x2 x3⁻¹ x4 x5⁻¹ x6`  and  `wordB c = x1 x2⁻¹ x3 x4⁻¹ x5 x6⁻¹`,

with `xi = sel (d_{i-1})`. The predicates `okA c n`, `okB c n` say that the word is the element with index `n`.
The certificate tables are the stage modules `D8D7.Stage00 … Stage11`, which are generated by
research/lean-haarD/gen_d8D7.py. Each stage is checked by `decide +kernel`. -/

namespace BipartiteDD.Haar.D8D7

open BipartiteDD.Haar.SL19Z3

/-- The connection set, as elements `(M, z)` of `SL(2,19) × Z_3`. -/
def sVec : List Grp :=
  [{svec}]

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

theorem digit_lt (c k : ℕ) : digit c k < 8 := Nat.mod_lt _ (by norm_num)

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

end BipartiteDD.Haar.D8D7
"""

COVER = """import BipartiteDD.Haar.D8D7.Check
{imports}

/-! Covering hypotheses of the (8,7) record: every element of `SL(2, 19) × Z_3` is an A-word and a B-word
in the connection set `SS`, by the kernel-checked certificates of the stage modules. Generated by
research/lean-haarD/gen_d8D7.py. Do not edit by hand. -/

namespace BipartiteDD.Haar.D8D7

open BipartiteDD.Haar.SL19Z3

/-- Every index `n < 20520` has an A-code. -/
theorem exA (n : ℕ) (hn : n < 20520) : ∃ c, okA c n = true := by
  obtain ⟨k, hk⟩ : ∃ k, n / {stage} = k := ⟨_, rfl⟩
  have hk12 : k < {stages} := by omega
  rcases (show {ors} by omega) with {alts}
{casesA}

/-- Every index `n < 20520` has a B-code. -/
theorem exB (n : ℕ) (hn : n < 20520) : ∃ c, okB c n = true := by
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

end BipartiteDD.Haar.D8D7
"""


def svec_text(S):
    items = []
    for a, b, c, d, z in S:
        items.append("(⟨%d, %d, %d, %d, by decide⟩, Multiplicative.ofAdd %d)" % (a, b, c, d, z))
    return (",\n    ").join(items)


def cover_text():
    imports = "\n".join("import BipartiteDD.Haar.D8D7.Stage%02d" % k for k in range(STAGES))
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


def pack(codes):
    v = 0
    for i, c in enumerate(codes):
        assert 0 <= c < 2 ** CODE_BITS
        v |= c << (CODE_BITS * i)
    return v


def emit_lean(S, digits, outdir):
    os.makedirs(outdir, exist_ok=True)
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
    with open(os.path.join(outdir, "Check.lean"), "w") as f:
        f.write(CHECK.replace("{svec}", svec_text(S)))


def main():
    sol, outdir = sys.argv[1], sys.argv[2]
    S = parse_sol(sol)
    check_group_numbering()
    digits = find_words(S)
    verify(S, digits)
    os.makedirs(outdir, exist_ok=True)
    with open(os.path.join(outdir, "codes.json"), "w") as f:
        json.dump({"S": S, "A": digits["A"], "B": digits["B"]}, f)
    emit_lean(S, digits, os.path.join(outdir, "lean"))
    print("S =", S)
    print("verified A and B words (3 pairs each) for all", N, "elements")


if __name__ == "__main__":
    main()
