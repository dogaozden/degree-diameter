#!/usr/bin/env python3
"""Covering certificates for the (5,9) record: G = meta 595 24 53 = Z_595 x|_53 Z_24 (order 14280).

Numbering (must match lean/BipartiteDD/Haar/LiftB/Meta595.lean): the element (a, j) has index a*24 + j in [0, 14280),
and (a, j)(b, l) = (a + 53^j b, j + l) mod (595, 24). This is the numbering of research/lifts/sols/haar/ (idx = a*k + j).

S is read from research/lifts/sols/d5D9_n28560_haar_meta595_24_53.txt (the "e 0 1 = a,j" lines) and cross-checked against
research/lifts/sols/haar/hc_d5D9_meta_595_24_53_1_s1.txt (the "idx meta(a=..,j=..)" lines). Five elements, degree 5.

Covering words. For every g in G there are two words of four pairs (digits d0..d7 in 0..4, indices into S):
  A-word: g = P(d0,d1) P(d2,d3) P(d4,d5) P(d6,d7),   P(x,y) = s_x^-1 s_y
  B-word: g = Q(d0,d1) Q(d2,d3) Q(d4,d5) Q(d6,d7),   Q(x,y) = s_x s_y^-1
This is the eight-letter form of `Haar/Diam9.lean`. The code is sum_k d_k 5^k (< 5^8 = 390625 < 2^19).
Entry n of the A (resp. B) table is the code of the A (resp. B) word of the element with index n.
Every word is re-checked by direct sequential multiplication before anything is written.

Usage: python3 gen_lift59.py SOL.txt HAAR.txt CODEDIR [LEANDIR]
writes CODEDIR/codes.json and LEANDIR/{Check,Stage00..Stage09,Cover}.lean (LEANDIR defaults to lean/BipartiteDD/Haar/LiftB).
"""
import json
import os
import re
import sys

import numpy as np

M = 595
K = 24
R = 53
N = M * K  # 14280
NS = 5
NPAIR = 4
STAGES = 10
STAGE = N // STAGES  # 1428
BITS = 19
assert STAGE * STAGES == N
assert NS ** (2 * NPAIR) < 2 ** BITS

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.normpath(os.path.join(HERE, "..", ".."))
DEFAULT_LEANDIR = os.path.join(REPO, "lean", "BipartiteDD", "Haar", "LiftB")


def mul(x, y):
    a, j = x
    b, l = y
    return ((a + pow(R, j, M) * b) % M, (j + l) % K)


def inv(x):
    a, j = x
    l = (-j) % K
    return ((-pow(R, l, M) * a) % M, l)


def enc(x):
    return x[0] * K + x[1]


def dec(n):
    return (n // K, n % K)


def parse_sol(path):
    lines = [ln.strip() for ln in open(path) if ln.strip() and not ln.startswith("#")]
    head = lines[0].split()
    assert head[:5] == ["lift", "D", "9", "Delta", "5"], head
    S = []
    for ln in lines:
        m = re.fullmatch(r"e 0 1 = (\d+),(\d+)", ln)
        if m:
            S.append((int(m.group(1)), int(m.group(2))))
    assert len(S) == NS and len(set(S)) == NS, S
    return S


def parse_haar(path):
    lines = [ln.strip() for ln in open(path) if ln.strip()]
    head = lines[0].split()
    assert head[:6] == ["5", "9", "meta", str(M), str(K), str(R)] and head[9] == str(N), head
    S = []
    for ln in lines[1:]:
        m = re.fullmatch(r"(\d+)\s+meta\(a=(\d+),j=(\d+)\)\s+z=0", ln)
        if m:
            idx, a, j = map(int, m.groups())
            assert idx == a * K + j and 0 <= a < M and 0 <= j < K, ln
            S.append((a, j))
    return S


def check_group():
    for n in range(N):
        assert enc(dec(n)) == n
    for a in range(0, M, 5):
        for j in range(K):
            x = (a, j)
            assert mul(x, inv(x)) == (0, 0) and mul(inv(x), x) == (0, 0), x
    for x in [(1, 2), (100, 14), (594, 3), (5, 0)]:
        for y in [(3, 7), (250, 1), (0, 13)]:
            for z in [(17, 9), (200, 5), (1, 0)]:
                assert mul(mul(x, y), z) == mul(x, mul(y, z))
    assert pow(R, K, M) == 1
    assert pow(R, 24, M) == 1 and all(pow(R, t, M) != 1 for t in range(1, 24))


def word_value(S, digs, side):
    el = (0, 0)
    for p in range(NPAIR):
        x, y = digs[2 * p], digs[2 * p + 1]
        if side == "A":
            el = mul(el, mul(inv(S[x]), S[y]))
        else:
            el = mul(el, mul(S[x], inv(S[y])))
    return el


def find_words(S):
    """For each index n, the A and B digit tuples (d0..d7) of a covering word.

    Meet in the middle: g = X Y with X = P P (a two-pair product, from a table of 25^2 entries) and Y = P P.
    For each Y, X = g Y^-1 is computed for all g at once and looked up in the table."""
    Sinv = [inv(s) for s in S]
    GA = np.array([dec(n)[0] for n in range(N)], dtype=np.int64)
    GJ = np.array([dec(n)[1] for n in range(N)], dtype=np.int64)
    Rpow = np.array([pow(R, j, M) for j in range(K)], dtype=np.int64)
    results = {}
    for side in ("A", "B"):
        P = {}
        for x in range(NS):
            for y in range(NS):
                P[(x, y)] = mul(Sinv[x], S[y]) if side == "A" else mul(S[x], Sinv[y])
        table = {}
        for (x1, y1), p1 in P.items():
            for (x2, y2), p2 in P.items():
                table.setdefault(enc(mul(p1, p2)), (x1, y1, x2, y2))
        mask = np.zeros(N, dtype=bool)
        mask[list(table.keys())] = True
        words = {}
        for (x3, y3), p3 in P.items():
            for (x4, y4), p4 in P.items():
                yel = mul(p3, p4)
                ya, yj = inv(yel)
                Xa = (GA + Rpow[GJ] * ya) % M
                Xj = (GJ + yj) % K
                Xn = Xa * K + Xj
                hit = mask[Xn]
                for n in np.nonzero(hit)[0]:
                    n = int(n)
                    if n not in words:
                        words[n] = list(table[int(Xn[n])]) + [x3, y3, x4, y4]
        assert len(words) == N, (side, N - len(words))
        results[side] = [words[n] for n in range(N)]
    return results


def verify(S, digits):
    for side in ("A", "B"):
        for n in range(N):
            assert word_value(S, digits[side][n], side) == dec(n), (side, n)


def code_of(digs):
    return sum(d * 5 ** k for k, d in enumerate(digs))


def pack(codes):
    v = 0
    for i, c in enumerate(codes):
        assert 0 <= c < 2 ** BITS
        v |= c << (BITS * i)
    return v


LEAN_CHECK = """import BipartiteDD.Haar.LiftB.Meta595

/-! The covering certificates of the (5,9) Haar record on `Z_595 ⋊ Z_24`, checked by kernel computation.

The connection set `S` is the five elements of `research/lifts/sols/d5D9_n28560_haar_meta595_24_53.txt`. For each
index `n < 14280` a code `c` (a base-5 number with digits `d0 … d7`) gives two words:

  `wordA c = x1⁻¹ x2 x3⁻¹ x4 x5⁻¹ x6 x7⁻¹ x8`  and  `wordB c = x1 x2⁻¹ x3 x4⁻¹ x5 x6⁻¹ x7 x8⁻¹`,

with `xi = sel (d_{i-1})`. The predicates `okA c n`, `okB c n` say that the word is the element with index `n`.
The certificate tables are the stage modules `LiftB.Stage00 … Stage09`, which are generated by
research/lean-haarD/gen_lift59.py. Each stage is checked by `decide +kernel`. -/

namespace BipartiteDD.Haar.LiftB

open BipartiteDD.Haar.LiftB.Meta595

/-- The connection set, as elements `(a, j)` of `Z_595 ⋊ Z_24`, in the order of the sol file. -/
def sVec : List Grp :=
  [⟨0, 0⟩, ⟨556, 1⟩, ⟨172, 11⟩, ⟨75, 23⟩, ⟨170, 5⟩]

/-- The `j`-th element of `S`, for `j < 5`. -/
def sel (j : ℕ) : Grp := sVec.getD j 1

/-- `S` as a finset. -/
def SS : Finset Grp := sVec.toFinset

theorem card_SS : SS.card = 5 := by decide +kernel

theorem sel_mem_all : (List.range 5).all (fun j => decide (sel j ∈ SS)) = true := by
  decide +kernel

theorem sel_mem (j : ℕ) (hj : j < 5) : sel j ∈ SS := by
  have h := List.all_eq_true.mp sel_mem_all j (List.mem_range.mpr hj)
  simpa using h

/-- The digit `k` of the code `c`, in base 5. -/
def digit (c k : ℕ) : ℕ := c / 5 ^ k % 5

theorem digit_lt (c k : ℕ) : digit c k < 5 := Nat.mod_lt _ (by norm_num)

/-- The A-word of the code `c`: `x1⁻¹ x2 x3⁻¹ x4 x5⁻¹ x6 x7⁻¹ x8`. -/
def wordA (c : ℕ) : Grp :=
  (sel (digit c 0))⁻¹ * sel (digit c 1) * (sel (digit c 2))⁻¹ * sel (digit c 3) *
    (sel (digit c 4))⁻¹ * sel (digit c 5) * (sel (digit c 6))⁻¹ * sel (digit c 7)

/-- The B-word of the code `c`: `x1 x2⁻¹ x3 x4⁻¹ x5 x6⁻¹ x7 x8⁻¹`. -/
def wordB (c : ℕ) : Grp :=
  sel (digit c 0) * (sel (digit c 1))⁻¹ * sel (digit c 2) * (sel (digit c 3))⁻¹ *
    sel (digit c 4) * (sel (digit c 5))⁻¹ * sel (digit c 6) * (sel (digit c 7))⁻¹

/-- The code `c` gives the A-word of the element with index `n`. -/
def okA (c n : ℕ) : Bool := decide (grpOf n = wordA c)

/-- The code `c` gives the B-word of the element with index `n`. -/
def okB (c n : ℕ) : Bool := decide (grpOf n = wordB c)

/-- A stage table is a natural number `C` holding `len` codes, `19` bits each, the code `i` in bits
`[19 i, 19 i + 19)`. Every code is below `5 ^ 8 < 2 ^ 19`. -/
def codeAt (C i : ℕ) : ℕ := (C >>> (19 * i)) % 524288

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

end BipartiteDD.Haar.LiftB
"""

LEAN_STAGE = """import BipartiteDD.Haar.LiftB.Check

/-! Covering certificates, stage {k} of {stages}: the indices `{lo} ≤ n < {hi}` of the (5,9) record on
`Z_595 ⋊ Z_24`. Generated by research/lean-haarD/gen_lift59.py. Do not edit by hand.

`stageA{k}` (resp. `stageB{k}`) packs the base-5 codes of the A-words (resp. B-words) of the elements with indices
`{lo} ≤ n < {hi}`: the code of index `{lo} + i` is `codeAt stageA{k} i`, 19 bits each. -/

namespace BipartiteDD.Haar.LiftB

def stageA{k} : ℕ := {a}

def stageB{k} : ℕ := {b}

set_option maxRecDepth 100000 in
theorem certA{k} : chkA {lo} {len} stageA{k} = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem certB{k} : chkB {lo} {len} stageB{k} = true := by decide +kernel

end BipartiteDD.Haar.LiftB
"""


def cover_text():
    imports = "\n".join("import BipartiteDD.Haar.LiftB.Stage%02d" % k for k in range(STAGES))
    ors = " ∨ ".join("k = %d" % k for k in range(STAGES))
    alts = " | ".join("h%d" % k for k in range(STAGES))
    cases = {}
    for side in ("A", "B"):
        lines = []
        for k in range(STAGES):
            lines.append("  · exact stageEx%s %d %d stage%s%02d cert%s%02d n (by omega) (by omega)"
                         % (side, k * STAGE, STAGE, side, k, side, k))
        cases[side] = "\n".join(lines)
    return """import BipartiteDD.Haar.LiftB.Check
{imports}

/-! Covering hypotheses of the (5,9) record: every element of `Z_595 ⋊ Z_24` is an A-word and a B-word in the
connection set `SS`, by the kernel-checked certificates of the stage modules. Generated by
research/lean-haarD/gen_lift59.py. Do not edit by hand. -/

namespace BipartiteDD.Haar.LiftB

open BipartiteDD.Haar.LiftB.Meta595

/-- Every index `n < {N}` has an A-code. -/
theorem exA (n : ℕ) (hn : n < {N}) : ∃ c, okA c n = true := by
  obtain ⟨k, hk⟩ : ∃ k, n / {STAGE} = k := ⟨_, rfl⟩
  have hk10 : k < {STAGES} := by omega
  rcases (show ({ors}) by omega) with {alts}
{casesA}

/-- Every index `n < {N}` has a B-code. -/
theorem exB (n : ℕ) (hn : n < {N}) : ∃ c, okB c n = true := by
  obtain ⟨k, hk⟩ : ∃ k, n / {STAGE} = k := ⟨_, rfl⟩
  have hk10 : k < {STAGES} := by omega
  rcases (show ({ors}) by omega) with {alts}
{casesB}

theorem cover1 : ∀ g : Grp, ∃ x1 ∈ SS, ∃ x2 ∈ SS, ∃ x3 ∈ SS, ∃ x4 ∈ SS, ∃ x5 ∈ SS, ∃ x6 ∈ SS,
    ∃ x7 ∈ SS, ∃ x8 ∈ SS, g = x1⁻¹ * x2 * x3⁻¹ * x4 * x5⁻¹ * x6 * x7⁻¹ * x8 := by
  intro g
  obtain ⟨c, hc⟩ := exA (enc g) (enc_lt g)
  have h : grpOf (enc g) = wordA c := of_decide_eq_true hc
  rw [grpOf_enc] at h
  exact ⟨_, sel_mem _ (digit_lt c 0), _, sel_mem _ (digit_lt c 1), _, sel_mem _ (digit_lt c 2),
    _, sel_mem _ (digit_lt c 3), _, sel_mem _ (digit_lt c 4), _, sel_mem _ (digit_lt c 5),
    _, sel_mem _ (digit_lt c 6), _, sel_mem _ (digit_lt c 7), h⟩

theorem cover2 : ∀ g : Grp, ∃ x1 ∈ SS, ∃ x2 ∈ SS, ∃ x3 ∈ SS, ∃ x4 ∈ SS, ∃ x5 ∈ SS, ∃ x6 ∈ SS,
    ∃ x7 ∈ SS, ∃ x8 ∈ SS, g = x1 * x2⁻¹ * x3 * x4⁻¹ * x5 * x6⁻¹ * x7 * x8⁻¹ := by
  intro g
  obtain ⟨c, hc⟩ := exB (enc g) (enc_lt g)
  have h : grpOf (enc g) = wordB c := of_decide_eq_true hc
  rw [grpOf_enc] at h
  exact ⟨_, sel_mem _ (digit_lt c 0), _, sel_mem _ (digit_lt c 1), _, sel_mem _ (digit_lt c 2),
    _, sel_mem _ (digit_lt c 3), _, sel_mem _ (digit_lt c 4), _, sel_mem _ (digit_lt c 5),
    _, sel_mem _ (digit_lt c 6), _, sel_mem _ (digit_lt c 7), h⟩

end BipartiteDD.Haar.LiftB
""".replace("{imports}", imports).replace("{ors}", ors).replace("{alts}", alts) \
    .replace("{casesA}", cases["A"]).replace("{casesB}", cases["B"]) \
    .replace("{N}", str(N)).replace("{STAGE}", str(STAGE)).replace("{STAGES}", str(STAGES))


def emit_lean(digits, leandir):
    os.makedirs(leandir, exist_ok=True)
    with open(os.path.join(leandir, "Check.lean"), "w") as f:
        f.write(LEAN_CHECK)
    for k in range(STAGES):
        lo = k * STAGE
        hi = lo + STAGE
        ca = [code_of(digits["A"][n]) for n in range(lo, hi)]
        cb = [code_of(digits["B"][n]) for n in range(lo, hi)]
        text = LEAN_STAGE.format(k="%02d" % k, stages=STAGES, lo=lo, hi=hi, len=STAGE,
                                 a="0x%x" % pack(ca), b="0x%x" % pack(cb))
        with open(os.path.join(leandir, "Stage%02d.lean" % k), "w") as f:
            f.write(text)
    with open(os.path.join(leandir, "Cover.lean"), "w") as f:
        f.write(cover_text())


def main():
    sol, haar, codedir = sys.argv[1], sys.argv[2], sys.argv[3]
    leandir = sys.argv[4] if len(sys.argv) > 4 else DEFAULT_LEANDIR
    S = parse_sol(sol)
    assert parse_haar(haar) == S, "sol and haar files disagree on S"
    check_group()
    digits = find_words(S)
    verify(S, digits)
    os.makedirs(codedir, exist_ok=True)
    with open(os.path.join(codedir, "codes.json"), "w") as f:
        json.dump({"S": S, "A": digits["A"], "B": digits["B"]}, f)
    emit_lean(digits, leandir)
    print("S =", S)
    print("verified A and B words for all", N, "elements; wrote", leandir)


if __name__ == "__main__":
    main()
