#!/usr/bin/env python3
"""Covering certificates for the (5,7) Haar record: G = PGL(2,5) x Z_13 (order 1560), Haar graph on 3120 vertices.

Numbering (must match lean/BipartiteDD/Haar/D5D7b/Group.lean). An element of PGL(2,5) is a matrix [[a,b],[c,d]] over
GF(5) with det != 0, modulo nonzero scalars; the representative has leading entry 1, the leading entry being a when
a != 0 and c otherwise. Its index is
  a = 1:           (c * 5 + b) * 4 + ((d - b c - 1) mod 5)            for n in [0, 100)
  a = 0, c = 1:    100 + (b - 1) * 5 + d                              for n in [100, 120)
The element (M, z) of G = PGL(2,5) x Z_13 has index 13 * enc(M) + z, in [0, 1560).
Products: matrix product in PGL(2,5), and addition in Z_13 (direct product), as in build_haar2.py.

S is read from research/lifts/sols/haar/hc_d5D7_pgl_5_13_s1.txt (five elements, degree 5). The sol file writes
mat(a,b,c,d) for [[a,b],[c,d]] and z for the Z_13 coordinate; build_haar2.py uses the same reading.

Covering words. For every g in G there are two words of three pairs (digits d0..d5 in 0..4, indices into S):
  A-word: g = S[d0]^-1 S[d1] S[d2]^-1 S[d3] S[d4]^-1 S[d5]
  B-word: g = S[d0] S[d1]^-1 S[d2] S[d3]^-1 S[d4] S[d5]^-1
This is the odd case D = 2 n + 1 = 7 of GraphD.lean with n = 3 (Diam7.lean). The code is sum_k d_k 5^k < 5^6 = 15625 < 2^16.
Entry n of the A (resp. B) table is the code of the A (resp. B) word of the element with index n. Every word is
re-checked by direct multiplication, and the diameter of the Haar graph is checked by two BFS.

Usage: python3 gen_d5D7b.py SOL.txt OUTDIR
writes OUTDIR/codes.json and OUTDIR/lean/Words.lean, Check.lean, Stage{00..05}.lean and Cover.lean.
The Lean files are copied to lean/BipartiteDD/Haar/D5D7b/ by hand (the generator does not touch the repo).
"""
import itertools
import json
import os
import re
import sys
from collections import deque

P = 5
Z = 13
NPGL = 120
N = NPGL * Z  # 1560
NS = 5
NPAIR = 3
STAGES = 6
STAGE = N // STAGES  # 260
BITS = 16
assert STAGE * STAGES == N
assert 5 ** (2 * NPAIR) < 2 ** BITS


def inv5(x):
    return pow(x, P - 2, P) if x % P else 0


def normalize(a, b, c, d):
    """Representative with leading entry 1: leading = a if a != 0 else c."""
    lead = a if a % P else c
    lam = inv5(lead)
    return tuple((lam * t) % P for t in (a, b, c, d))


def enc(M):
    a, b, c, d = M
    if a == 1:
        k = (d - b * c - 1) % P
        assert k < P - 1
        return (c * P + b) * (P - 1) + k
    assert a == 0 and c == 1 and b != 0
    return P * (P - 1) * P + (b - 1) * P + d  # 100 + (b-1)*5 + d


def dec(n):
    if n < P * P * (P - 1):
        k = n % (P - 1)
        cb = n // (P - 1)
        c, b = divmod(cb, P)
        return (1, b, c, (b * c + 1 + k) % P)
    m = n - P * P * (P - 1)
    b, d = divmod(m, P)
    return (0, b + 1, 1, d)


def mat_mul(M, N_):
    a, b, c, d = M
    e, f, g, h = N_
    return normalize((a * e + b * g) % P, (a * f + b * h) % P, (c * e + d * g) % P, (c * f + d * h) % P)


def mat_inv(M):
    a, b, c, d = M
    det = (a * d - b * c) % P
    di = inv5(det)
    return normalize((d * di) % P, (-b * di) % P, (-c * di) % P, (a * di) % P)


def check_pgl():
    els = [dec(n) for n in range(NPGL)]
    assert len(set(els)) == NPGL
    for n, M in enumerate(els):
        assert enc(M) == n, (n, M)
        a, b, c, d = M
        assert (a * d - b * c) % P != 0
        assert normalize(*M) == M
    ident = (1, 0, 0, 1)
    for n in range(NPGL):
        M = els[n]
        assert mat_mul(M, mat_inv(M)) == ident and mat_mul(mat_inv(M), M) == ident
    # all classes of det != 0 are hit: count matrices of det != 0 modulo scalars
    seen = set()
    for a, b, c, d in itertools.product(range(P), repeat=4):
        if (a * d - b * c) % P:
            seen.add(normalize(a, b, c, d))
    assert seen == set(els)
    for x, y, w in [(els[5], els[77], els[119]), (els[1], els[2], els[50]), (els[99], els[100], els[13])]:
        assert mat_mul(mat_mul(x, y), w) == mat_mul(x, mat_mul(y, w))


def parse_sol(path):
    lines = [ln.strip() for ln in open(path) if ln.strip()]
    head = lines[0].split()
    assert head[:6] == ["5", "7", "pgl", str(P), "n", str(Z)] and int(head[head.index("N") + 1]) == N, head
    S = []
    for ln in lines[1:1 + NS]:
        m = re.fullmatch(r"\d+\s+mat\((\d+),(\d+),(\d+),(\d+)\)\s+z=(\d+)", ln)
        assert m, ln
        a, b, c, d, z = map(int, m.groups())
        assert (a * d - b * c) % P != 0 and 0 <= z < Z
        S.append((normalize(a, b, c, d), z))
    assert len(S) == NS and len(set(S)) == NS, S
    return S


def el_index(g):
    M, z = g
    return enc(M) * Z + z


def g_mul(x, y):
    return (mat_mul(x[0], y[0]), (x[1] + y[1]) % Z)


def g_inv(x):
    return (mat_inv(x[0]), (-x[1]) % Z)


def g_of_index(n):
    return (dec(n // Z), n % Z)


def check_group():
    for n in range(N):
        assert el_index(g_of_index(n)) == n
    for n in range(0, N, 37):
        x = g_of_index(n)
        assert g_mul(x, g_inv(x)) == ((1, 0, 0, 1), 0)


def word_value(S, digs, side):
    el = ((1, 0, 0, 1), 0)
    for p in range(NPAIR):
        x, y = S[digs[2 * p]], S[digs[2 * p + 1]]
        if side == "A":
            el = g_mul(el, g_mul(g_inv(x), y))
        else:
            el = g_mul(el, g_mul(x, g_inv(y)))
    return el


def find_words(S):
    """For each index n, the A and B digit tuples (d0..d5) of a covering word."""
    results = {}
    for side in ("A", "B"):
        words = {}
        for digs in itertools.product(range(NS), repeat=2 * NPAIR):
            el = word_value(S, digs, side)
            words.setdefault(el_index(el), digs)
        missing = N - len(words)
        assert missing == 0, (side, missing)
        results[side] = [words[n] for n in range(N)]
    return results


def verify(S, digits):
    for side in ("A", "B"):
        for n in range(N):
            assert word_value(S, digits[side][n], side) == g_of_index(n), (side, n)


def haar_diameter(S):
    """Diameter of the Haar graph on G + G: inl g ~ inr (s g) for s in S. Two BFS from each side's identity."""
    # index: A-vertex g -> g, B-vertex h -> N + h
    gs = [g_of_index(n) for n in range(N)]
    adj = [[] for _ in range(2 * N)]
    for n in range(N):
        g = gs[n]
        for s in S:
            h = el_index(g_mul(s, g))
            adj[n].append(N + h)
            adj[N + h].append(n)
    assert all(len(a) == NS and len(set(a)) == NS for a in adj), "not NS-regular with distinct neighbours"
    diam = 0
    for src in range(2 * N):
        dist = [-1] * (2 * N)
        dist[src] = 0
        q = deque([src])
        while q:
            v = q.popleft()
            for w in adj[v]:
                if dist[w] < 0:
                    dist[w] = dist[v] + 1
                    q.append(w)
        assert min(dist) >= 0, "disconnected"
        diam = max(diam, max(dist))
    return diam


LEAN_WORDS = """import BipartiteDD.Haar.D5D7b.Group

/-! The two six-letter words of the (5,7) record, written once for any group.

`wordA6 x₁ … x₆ = x₁⁻¹ x₂ x₃⁻¹ x₄ x₅⁻¹ x₆` and `wordB6 x₁ … x₆ = x₁ x₂⁻¹ x₃ x₄⁻¹ x₅ x₆⁻¹` are the two products of
`Diam7` (the hypotheses `hA`, `hB` of `ediam_le_seven_of`). `CoverA S` and `CoverB S` are those hypotheses with
the bodies written out, so `cover1 : CoverA SS` is passed to the lemma without unfolding the instance path (see
`research/lean-haarD/STATUS-d5D7b.md`). Generated by research/lean-haarD/gen_d5D7b.py. Do not edit by hand. -/

namespace BipartiteDD.Haar.D5D7b

/-- `x₁⁻¹ x₂ x₃⁻¹ x₄ x₅⁻¹ x₆`, in any group. -/
def wordA6 {G : Type*} [Group G] (x₁ x₂ x₃ x₄ x₅ x₆ : G) : G := x₁⁻¹ * x₂ * x₃⁻¹ * x₄ * x₅⁻¹ * x₆

/-- `x₁ x₂⁻¹ x₃ x₄⁻¹ x₅ x₆⁻¹`, in any group. -/
def wordB6 {G : Type*} [Group G] (x₁ x₂ x₃ x₄ x₅ x₆ : G) : G := x₁ * x₂⁻¹ * x₃ * x₄⁻¹ * x₅ * x₆⁻¹

/-- The A-covering hypothesis of `Diam7`: every `g` is an A-word in `S`. -/
def CoverA {G : Type*} [Group G] (S : Finset G) : Prop :=
  ∀ g : G, ∃ x₁ ∈ S, ∃ x₂ ∈ S, ∃ x₃ ∈ S, ∃ x₄ ∈ S, ∃ x₅ ∈ S, ∃ x₆ ∈ S,
    g = x₁⁻¹ * x₂ * x₃⁻¹ * x₄ * x₅⁻¹ * x₆

/-- The B-covering hypothesis of `Diam7`: every `g` is a B-word in `S`. -/
def CoverB {G : Type*} [Group G] (S : Finset G) : Prop :=
  ∀ g : G, ∃ x₁ ∈ S, ∃ x₂ ∈ S, ∃ x₃ ∈ S, ∃ x₄ ∈ S, ∃ x₅ ∈ S, ∃ x₆ ∈ S,
    g = x₁ * x₂⁻¹ * x₃ * x₄⁻¹ * x₅ * x₆⁻¹

end BipartiteDD.Haar.D5D7b
"""


LEAN_CHECK = """import BipartiteDD.Haar.D5D7b.Words

/-! The covering certificates of the (5,7) Haar record on `PGL(2, 5) × Z_13`, checked by kernel computation.

The connection set `S` is the five elements of `research/lifts/sols/haar/hc_d5D7_pgl_5_13_s1.txt`, written as
`(class of [[a, b], [c, d]], z)`. For each index `n < 1560` a code `c` (a base-5 number with digits `d0 … d5`) gives two
words:

  `wordA c = x1⁻¹ x2 x3⁻¹ x4 x5⁻¹ x6`  and  `wordB c = x1 x2⁻¹ x3 x4⁻¹ x5 x6⁻¹`,

with `xi = sel (d_{{i-1}})`. The predicates `okA c n`, `okB c n` say that the word is the element with index `n`.
The certificate tables are the stage modules `D5D7b.Stage00 … Stage{last}`, generated by research/lean-haarD/gen_d5D7b.py.
Each stage is checked by `decide +kernel`. Generated by research/lean-haarD/gen_d5D7b.py. Do not edit by hand. -/

namespace BipartiteDD.Haar.D5D7b

open BipartiteDD.Haar.D5D7b.PGL5Z13

/-- The connection set, as elements `(M, z)` of `PGL(2, 5) × Z_13`, in the order of the sol file. -/
def sVec : List Grp :=
  [{svec}]

/-- The `j`-th element of `S`, for `j < 5`. -/
def sel (j : ℕ) : Grp := sVec.getD j 1

/-- `S` as a finset. -/
def SS : Finset Grp := sVec.toFinset

theorem card_SS : SS.card = {ns} := by decide +kernel

theorem sel_mem_all : (List.range {ns}).all (fun j => decide (sel j ∈ SS)) = true := by
  decide +kernel

theorem sel_mem (j : ℕ) (hj : j < {ns}) : sel j ∈ SS := by
  have h := List.all_eq_true.mp sel_mem_all j (List.mem_range.mpr hj)
  simpa using h

/-- The digit `k` of the code `c`, in base 5. -/
def digit (c k : ℕ) : ℕ := c / 5 ^ k % 5

theorem digit_lt (c k : ℕ) : digit c k < 5 := Nat.mod_lt _ (by norm_num)

/-- The A-word of the code `c`: `x1⁻¹ x2 x3⁻¹ x4 x5⁻¹ x6`. -/
def wordA (c : ℕ) : Grp :=
  wordA6 (sel (digit c 0)) (sel (digit c 1)) (sel (digit c 2)) (sel (digit c 3)) (sel (digit c 4)) (sel (digit c 5))

/-- The B-word of the code `c`: `x1 x2⁻¹ x3 x4⁻¹ x5 x6⁻¹`. -/
def wordB (c : ℕ) : Grp :=
  wordB6 (sel (digit c 0)) (sel (digit c 1)) (sel (digit c 2)) (sel (digit c 3)) (sel (digit c 4)) (sel (digit c 5))

/-- The code `c` gives the A-word of the element with index `n`. -/
def okA (c n : ℕ) : Bool := decide (grpOf n = wordA c)

/-- The code `c` gives the B-word of the element with index `n`. -/
def okB (c n : ℕ) : Bool := decide (grpOf n = wordB c)

/-- A stage table is a natural number `C` holding `len` codes, `16` bits each, the code `i` in bits
`[16 i, 16 i + 16)`. Every code is below `5 ^ 6 = 15625 < 2 ^ 16`. -/
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

end BipartiteDD.Haar.D5D7b
"""

LEAN_STAGE = """import BipartiteDD.Haar.D5D7b.Check

/-! Covering certificates, stage {k} of {stages}: the indices `{lo} ≤ n < {hi}` of the (5,7) record on
`PGL(2, 5) × Z_13`. Generated by research/lean-haarD/gen_d5D7b.py. Do not edit by hand.

`stageA{k}` (resp. `stageB{k}`) packs the base-5 codes of the A-words (resp. B-words) of the elements with indices
`{lo} ≤ n < {hi}`: the code of index `{lo} + i` is `codeAt stageA{k} i`, 16 bits each. -/

namespace BipartiteDD.Haar.D5D7b

def stageA{k} : ℕ := {a}

def stageB{k} : ℕ := {b}

set_option maxRecDepth 100000 in
theorem certA{k} : chkA {lo} {len} stageA{k} = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem certB{k} : chkB {lo} {len} stageB{k} = true := by decide +kernel

end BipartiteDD.Haar.D5D7b
"""

COVER = """import BipartiteDD.Haar.D5D7b.Check
import BipartiteDD.Haar.D5D7b.Words
{imports}

/-! Covering hypotheses of the (5,7) record: every element of `PGL(2, 5) × Z_13` is an A-word and a B-word in the
connection set `SS`, by the kernel-checked certificates of the stage modules. Generated by
research/lean-haarD/gen_d5D7b.py. Do not edit by hand. -/

namespace BipartiteDD.Haar.D5D7b

open BipartiteDD.Haar.D5D7b.PGL5Z13

/-- Every index `n < 1560` has an A-code. -/
theorem exA (n : ℕ) (hn : n < 1560) : ∃ c, okA c n = true := by
  obtain ⟨k, hk⟩ : ∃ k, n / {stage} = k := ⟨_, rfl⟩
  have hk12 : k < {stages} := by omega
  rcases (show {ors} by omega) with {alts}
{casesA}

/-- Every index `n < 1560` has a B-code. -/
theorem exB (n : ℕ) (hn : n < 1560) : ∃ c, okB c n = true := by
  obtain ⟨k, hk⟩ : ∃ k, n / {stage} = k := ⟨_, rfl⟩
  have hk12 : k < {stages} := by omega
  rcases (show {ors} by omega) with {alts}
{casesB}

theorem cover1 : CoverA SS := by
  unfold CoverA
  intro g
  obtain ⟨c, hc⟩ := exA (enc g) (enc_lt g)
  have h : grpOf (enc g) = wordA c := of_decide_eq_true hc
  rw [grpOf_enc] at h
  exact ⟨_, sel_mem _ (digit_lt c 0), _, sel_mem _ (digit_lt c 1), _, sel_mem _ (digit_lt c 2),
    _, sel_mem _ (digit_lt c 3), _, sel_mem _ (digit_lt c 4), _, sel_mem _ (digit_lt c 5), h⟩

theorem cover2 : CoverB SS := by
  unfold CoverB
  intro g
  obtain ⟨c, hc⟩ := exB (enc g) (enc_lt g)
  have h : grpOf (enc g) = wordB c := of_decide_eq_true hc
  rw [grpOf_enc] at h
  exact ⟨_, sel_mem _ (digit_lt c 0), _, sel_mem _ (digit_lt c 1), _, sel_mem _ (digit_lt c 2),
    _, sel_mem _ (digit_lt c 3), _, sel_mem _ (digit_lt c 4), _, sel_mem _ (digit_lt c 5), h⟩

end BipartiteDD.Haar.D5D7b
"""


def code_of(digs):
    return sum(d * 5 ** k for k, d in enumerate(digs))


def pack(codes):
    v = 0
    for i, c in enumerate(codes):
        assert 0 <= c < 2 ** BITS
        v |= c << (BITS * i)
    return v


def sol_vec_lean(S):
    items = []
    for M, z in S:
        a, b, c, d = M
        items.append("(PGL5.gZ %d %d %d %d, Multiplicative.ofAdd (%d : ZMod 13))" % (a, b, c, d, z))
    return ",\n   ".join(items)


def cover_text():
    imports = "\n".join("import BipartiteDD.Haar.D5D7b.Stage%02d" % k for k in range(STAGES))
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


def emit_lean(S, digits, outdir):
    os.makedirs(outdir, exist_ok=True)
    with open(os.path.join(outdir, "Words.lean"), "w") as f:
        f.write(LEAN_WORDS)
    with open(os.path.join(outdir, "Check.lean"), "w") as f:
        f.write(LEAN_CHECK.replace("{svec}", sol_vec_lean(S)).replace("{ns}", str(NS))
                .replace("{last}", "%02d" % (STAGES - 1)))
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
    check_pgl()
    S = parse_sol(sol)
    check_group()
    diam = haar_diameter(S)
    print("S =", S)
    print("Haar graph on", 2 * N, "vertices, diameter", diam)
    assert diam <= 7
    digits = find_words(S)
    verify(S, digits)
    os.makedirs(outdir, exist_ok=True)
    with open(os.path.join(outdir, "codes.json"), "w") as f:
        json.dump({"S": [[list(M), z] for M, z in S], "A": digits["A"], "B": digits["B"]}, f)
    emit_lean(S, digits, os.path.join(outdir, "lean"))
    print("verified A and B words for all", N, "elements")


if __name__ == "__main__":
    main()
