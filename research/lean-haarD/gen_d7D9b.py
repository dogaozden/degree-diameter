#!/usr/bin/env python3
"""Covering certificates for the (7,9) record of 462,840 vertices: G = PSL(2,29) x Z_19 (order 231420),
S from research/frontier/sols/d7D9_psl_29_19_orb3_s1.txt (Haar graph on 462840 vertices, degree 7, diameter 9).

Numbering (must match lean/BipartiteDD/Haar/D7D9b/PSL29.lean and Base.lean):
  PSL(2,29) class of [[a,b],[c,d]] (det 1, mod +-1) has the representative with posB(a,c): a <= 14 when c = 0,
  c <= 14 otherwise. Its index enc(a,b,c,d) in [0, 12180):
    c = 0:  (a-1)*29 + b                       (a in 1..14, b in 0..28; 406 elements)
    c != 0: 406 + ((c-1)*29 + a)*29 + d         (c in 1..14; 11774 elements)
  G element (P, z) has index n = 19*enc(P) + z.

Certificates. For every g in G, two words of four pairs (digits d0..d7 in 0..6, indices into S):
  A-word: g = P(d0,d1) P(d2,d3) P(d4,d5) P(d6,d7),   P(x,y) = s_x^-1 s_y
  B-word: g = Q(d0,d1) Q(d2,d3) Q(d4,d5) Q(d6,d7),   Q(x,y) = s_x s_y^-1
The code is sum_k d_k 7^k (< 7^8 < 2^23). Entry n of the A (resp. B) table is the code of the A (resp. B) word
of the element with index n. Every word is re-checked here by direct multiplication.

Stages: N = 231420 = 42 * 5510 indices per side, one stage module per block of 5510 indices (both sides).

Usage: python3 gen_d7D9b.py SOL.txt OUTDIR [PSL19_TEMPLATE]
writes OUTDIR/codes.json and OUTDIR/lean/{Stage00..41.lean, Cover.lean, Gens.lean, PSL29.lean}.
The Lean files are copied to lean/BipartiteDD/Haar/D7D9b/ by hand (the generator does not touch the repo).
PSL29.lean is the PSL(2,19) module of lean/BipartiteDD/Haar/D7D8/PSL19.lean with the prime changed to 29.
"""
import json
import os
import re
import sys

import numpy as np

Q = 29
NZ = 19
H = (Q - 1) // 2  # 14: representatives have first column entry <= H
C0 = H * Q  # 406: elements with c = 0
NSL = C0 + H * Q * Q  # 12180
N = NSL * NZ  # 231420
NS = 7
BASE = 7
BITS = 23
STAGES = 42
STAGE = N // STAGES  # 5510
assert NSL == 12180 and N == 231420
assert STAGE * STAGES == N
assert NS ** 8 < 2 ** BITS


def inv_mod(x):
    return pow(int(x) % Q, Q - 2, Q)


def posB(a, c):
    return a <= H if c == 0 else c <= H


def canon(a, b, c, d):
    if posB(a, c):
        return (a, b, c, d)
    return ((-a) % Q, (-b) % Q, (-c) % Q, (-d) % Q)


def enc_sl(a, b, c, d):
    assert posB(a, c) and (a * d - b * c) % Q == 1
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
    p, q, r, s = canon((a * e + b * g) % Q, (a * f + b * h) % Q, (c * e + d * g) % Q, (c * f + d * h) % Q)
    return (p, q, r, s, (z + w) % NZ)


def inv(x):
    a, b, c, d, z = x
    p, q, r, s = canon(d % Q, (-b) % Q, (-c) % Q, a % Q)
    return (p, q, r, s, (-z) % NZ)


def one():
    return (1, 0, 0, 1, 0)


def parse_sol(path):
    lines = [ln.strip() for ln in open(path) if ln.strip()]
    head = lines[0].split()
    assert head[2] == "psl" and int(head[3]) == Q and int(head[5]) == NZ and int(head[7]) == N, head
    S = []
    for ln in lines[1:]:
        m = re.fullmatch(r"\d+\s+mat\((\d+),(\d+),(\d+),(\d+)\)\s+z=(\d+)", ln)
        assert m, ln
        a, b, c, d, z = map(int, m.groups())
        assert (a * d - b * c) % Q == 1, ln
        p, q, r, s = canon(a % Q, b % Q, c % Q, d % Q)
        S.append((p, q, r, s, z % NZ))
    assert len(S) == NS and len(set(S)) == NS, S
    return S


def check_group_numbering():
    seen = set()
    for n in range(N):
        g = quad_g(n)
        a, b, c, d, z = g
        assert posB(a, c) and (a * d - b * c) % Q == 1, (n, g)
        assert enc_g(a, b, c, d, z) == n, (n, g)
        seen.add(g)
    assert len(seen) == N


def find_words(S):
    """For each index n, the A and B digit tuples (d0..d7) of its covering words (vectorised over n)."""
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
        # left half: two-pair products X, table[element index] = digits (x1, y1, x2, y2)
        table = {}
        for (x1, y1), p1 in P.items():
            for (x2, y2), p2 in P.items():
                table.setdefault(enc_g(*mul(p1, p2)), (x1, y1, x2, y2))
        mask = np.zeros(N, dtype=bool)
        mask[list(table.keys())] = True
        tab_code = np.zeros(N, dtype=np.int64)
        for k, dig in table.items():
            tab_code[k] = code_of(dig)
        # right half: two-pair products Y; then g = X Y with X = g Y^-1 in the table
        ylist = {}
        for (x3, y3) in P:
            for (x4, y4) in P:
                yel = mul(P[(x3, y3)], P[(x4, y4)])
                ylist.setdefault(enc_g(*yel), (yel, (x3, y3, x4, y4)))
        found = np.zeros(N, dtype=bool)
        left = np.zeros(N, dtype=np.int64)
        right = np.zeros(N, dtype=np.int64)
        for _, (yel, ydig) in ylist.items():
            ya, yb, yc, yd, yz = inv(yel)
            Xa = (A * ya + B * yc) % Q
            Xb = (A * yb + B * yd) % Q
            Xc = (C * ya + D * yc) % Q
            Xd = (C * yb + D * yd) % Q
            Xz = (Z + yz) % NZ
            pos = np.where(Xc == 0, Xa <= H, Xc <= H)
            Xa = np.where(pos, Xa, (-Xa) % Q)
            Xb = np.where(pos, Xb, (-Xb) % Q)
            Xc = np.where(pos, Xc, (-Xc) % Q)
            Xd = np.where(pos, Xd, (-Xd) % Q)
            Xn = NZ * np.where(Xc == 0, (Xa - 1) * Q + Xb, C0 + ((Xc - 1) * Q + Xa) * Q + Xd) + Xz
            hit = mask[Xn] & ~found
            left[hit] = tab_code[Xn[hit]]
            right[hit] = code_of(ydig)
            found |= hit
        assert found.all(), (side, int(N - found.sum()))
        out = []
        for n in range(N):
            lc = int(left[n])
            rc = int(right[n])
            lw = [(lc // BASE ** k) % BASE for k in range(4)]
            rw = [(rc // BASE ** k) % BASE for k in range(4)]
            out.append([lw[0], lw[1], lw[2], lw[3], rw[0], rw[1], rw[2], rw[3]])
        results[side] = out
    return results


def word_value(S, digs, side):
    el = one()
    for k in range(0, 8, 2):
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
            assert word_value(S, digits[side][n], side) == quad_g(n), (side, n)


LEAN_STAGE = """import BipartiteDD.Haar.D7D9b.Check

/-! Covering certificates, stage {k} of {stages}: the indices `{lo} ≤ n < {hi}` of the (7,9) record on
`PSL(2, 29) × Z_19`. Generated by research/lean-haarD/gen_d7D9b.py. Do not edit by hand.

`stageA{k}` (resp. `stageB{k}`) packs the base-7 codes of the A-words (resp. B-words) of the elements with indices
`{lo} ≤ n < {hi}`: the code of index `{lo} + i` is `codeAt stageA{k} i`, 23 bits each. -/

namespace BipartiteDD.Haar.D7D9b

def stageA{k} : ℕ := {a}

def stageB{k} : ℕ := {b}

set_option maxRecDepth 100000 in
theorem certA{k} : chkA {lo} {len} stageA{k} = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem certB{k} : chkB {lo} {len} stageB{k} = true := by decide +kernel

end BipartiteDD.Haar.D7D9b
"""

COVER = """import BipartiteDD.Haar.D7D9b.Check
{imports}

/-! Covering hypotheses of the (7,9) record: every element of `PSL(2, 29) × Z_19` is an A-word and a B-word
in the connection set `SS`, by the kernel-checked certificates of the stage modules. Generated by
research/lean-haarD/gen_d7D9b.py. Do not edit by hand. -/

namespace BipartiteDD.Haar.D7D9b

/-- Every index `n < 231420` has an A-code: `idxG (wordA c) = n`. -/
theorem exA (n : ℕ) (hn : n < 231420) : ∃ c, idxG (wordA c) = n := by
  obtain ⟨k, hk⟩ : ∃ k, n / {stage} = k := ⟨_, rfl⟩
  have hk12 : k < {stages} := by omega
  rcases (show {ors} by omega) with {alts}
{casesA}

/-- Every index `n < 231420` has a B-code: `idxG (wordB c) = n`. -/
theorem exB (n : ℕ) (hn : n < 231420) : ∃ c, idxG (wordB c) = n := by
  obtain ⟨k, hk⟩ : ∃ k, n / {stage} = k := ⟨_, rfl⟩
  have hk12 : k < {stages} := by omega
  rcases (show {ors} by omega) with {alts}
{casesB}

/-- The covering hypothesis `hA` of `Haar.haar_isBipartiteDegDiam9_of_equiv`, for a finite set `S` in any group. It is
the lemma's own body, so the lemma's hypothesis and `cover1` share one `Group` instance path. -/
def CoverHypA {G : Type*} [Group G] (S : Finset G) : Prop :=
  ∀ g : G, ∃ x1 ∈ S, ∃ x2 ∈ S, ∃ x3 ∈ S, ∃ x4 ∈ S, ∃ x5 ∈ S, ∃ x6 ∈ S, ∃ x7 ∈ S, ∃ x8 ∈ S,
    g = x1⁻¹ * x2 * x3⁻¹ * x4 * x5⁻¹ * x6 * x7⁻¹ * x8

/-- The covering hypothesis `hB` of `Haar.haar_isBipartiteDegDiam9_of_equiv`, for a finite set `S` in any group. -/
def CoverHypB {G : Type*} [Group G] (S : Finset G) : Prop :=
  ∀ g : G, ∃ x1 ∈ S, ∃ x2 ∈ S, ∃ x3 ∈ S, ∃ x4 ∈ S, ∃ x5 ∈ S, ∃ x6 ∈ S, ∃ x7 ∈ S, ∃ x8 ∈ S,
    g = x1 * x2⁻¹ * x3 * x4⁻¹ * x5 * x6⁻¹ * x7 * x8⁻¹

theorem cover1 : CoverHypA SS := by
  intro g
  obtain ⟨c, hc⟩ := exA (idxG g) (idxG_lt g)
  have h : wordA c = g := eq_of_idxG_eq hc
  exact ⟨_, sel_mem _ (digit_lt c 0), _, sel_mem _ (digit_lt c 1), _, sel_mem _ (digit_lt c 2),
    _, sel_mem _ (digit_lt c 3), _, sel_mem _ (digit_lt c 4), _, sel_mem _ (digit_lt c 5),
    _, sel_mem _ (digit_lt c 6), _, sel_mem _ (digit_lt c 7), h.symm⟩

theorem cover2 : CoverHypB SS := by
  intro g
  obtain ⟨c, hc⟩ := exB (idxG g) (idxG_lt g)
  have h : wordB c = g := eq_of_idxG_eq hc
  exact ⟨_, sel_mem _ (digit_lt c 0), _, sel_mem _ (digit_lt c 1), _, sel_mem _ (digit_lt c 2),
    _, sel_mem _ (digit_lt c 3), _, sel_mem _ (digit_lt c 4), _, sel_mem _ (digit_lt c 5),
    _, sel_mem _ (digit_lt c 6), _, sel_mem _ (digit_lt c 7), h.symm⟩

end BipartiteDD.Haar.D7D9b
"""

GENS = """import BipartiteDD.Haar.D7D9b.Base

/-! The seven connection generators `S` of the (7,9) record `462,840` (`research/frontier/sols/
d7D9_psl_29_19_orb3_s1.txt`), as elements `(P, z)` of `PSL(2, 29) × Z_19` in the normal form of `PSL29`.
Generated by research/lean-haarD/gen_d7D9b.py. Do not edit by hand. -/

namespace BipartiteDD.Haar.D7D9b

open BipartiteDD.Haar.PSL29

/-- The connection set, as elements `(P, z)`. -/
def sVec : List G :=
  [{items}]

/-- The `j`-th element of `S`, for `j < 7`. -/
def sel (j : ℕ) : G := sVec.getD j 1

/-- `S` as a finset. -/
def SS : Finset G := sVec.toFinset

theorem card_SS : SS.card = 7 := by decide +kernel

theorem sel_mem_all : (List.range 7).all (fun j => decide (sel j ∈ SS)) = true := by
  decide +kernel

theorem sel_mem (j : ℕ) (hj : j < 7) : sel j ∈ SS := by
  have h := List.all_eq_true.mp sel_mem_all j (List.mem_range.mpr hj)
  simpa using h

end BipartiteDD.Haar.D7D9b
"""


def gens_text(S):
    items = []
    for (a, b, c, d, z) in S:
        items.append("(⟨%d, %d, %d, %d, by decide, by decide⟩, Multiplicative.ofAdd (%d : ZMod %d))"
                     % (a, b, c, d, z, NZ))
    body = ",\n    ".join(items)
    return GENS.replace("{items}", body)


def cover_text():
    imports = "\n".join("import BipartiteDD.Haar.D7D9b.Stage%02d" % k for k in range(STAGES))
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
        assert 0 <= c < 2 ** BITS
        v |= c << (BITS * i)
    return v


def emit_lean(digits, outdir):
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


def psl29_text(template):
    """The PSL(2,19) group module with the prime changed to 29 (same proofs; the numbering constants are
    recomputed here: 406 = 14 * 29, 841 = 29 * 29, 12180 = 406 + 14 * 29 * 29, threshold 14)."""
    t = open(template).read()
    subs = [
        (r"\bPSL19\b", "PSL29"),
        (r"\bPSL\(2, 19\)", "PSL(2, 29)"),
        (r"zmod19", "zmod29"),
        (r"inv19", "inv29"),
        (r"\bZMod 19\b", "ZMod 29"),
        (r"\b19\b", "29"),
        (r"\b171\b", "406"),
        (r"\b361\b", "841"),
        (r"\b3420\b", "12180"),
        (r"≤ 9\b", "≤ 14"),
        (r"1…9\b", "1…14"),
        (r", 9\}", ", 14}"),
    ]
    for pat, rep in subs:
        t = re.sub(pat, rep, t)
    inv_tab = [0] + [inv_mod(x) for x in range(1, Q)]
    t, k = re.subn(r"def invTab : List \(ZMod 29\) := \[[^\]]*\]",
                   "def invTab : List (ZMod 29) := [" + ", ".join(map(str, inv_tab)) + "]", t)
    assert k == 1
    # the inverse-table lemmas by kernel evaluation (841 cases in the elaborator run out of memory)
    t, k = re.subn(r"(theorem inv29_(?:mul|eq) : [^\n]*:= by\n  )decide\n", r"\1decide +kernel\n", t)
    assert k == 2, k
    # the numbering facts for all n < 12180, from ten kernel checks of 1218 indices (the all-at-once check
    # over 12180 indices exhausts the memory of a 16 GB machine)
    start = t.index("set_option maxRecDepth 100000 in\ntheorem quad_valid")
    end = t.index("/-- The class with index")
    t = t[:start] + blocks_text() + t[end:]
    return t


BLOCK = 1218
NBLOCKS = NSL // BLOCK
assert BLOCK * NBLOCKS == NSL


def valid_pred(e):
    return ("(quad (%s)).1 * (quad (%s)).2.2.2 - (quad (%s)).2.1 * (quad (%s)).2.2.1 = 1 ∧ "
            "posB (quad (%s)).1 (quad (%s)).2.2.1 = true" % ((e,) * 6))


def enc_pred(e, rhs):
    return "enc (quad (%s)).1 (quad (%s)).2.1 (quad (%s)).2.2.1 (quad (%s)).2.2.2 = %s" % (e, e, e, e, rhs)


BLOCK_CASES = " ∨ ".join("k = %d" % k for k in range(NBLOCKS))
BLOCK_PATS = " | ".join(["rfl"] * NBLOCKS)


def blocks_text():
    """Lean text: `quad_valid` and `enc_of_quad` for all n < 12180, from ten kernel checks of 1218 indices each,
    joined by `all_of_blocks`."""
    out = []
    out.append("/-- Splitting `n < B * M` into blocks: `P` holds for all `n` once it holds on each block. -/\n"
               "theorem all_of_blocks {P : ℕ → Prop} (h : ∀ k < %d, ∀ m < %d, P (%d * k + m)) :\n"
               "    ∀ n < %d, P n := by\n"
               "  intro n hn\n"
               "  have h2 := h (n / %d) (by omega) (n %% %d) (Nat.mod_lt _ (by norm_num))\n"
               "  rwa [Nat.div_add_mod] at h2\n\n" % (NBLOCKS, BLOCK, BLOCK, NSL, BLOCK, BLOCK))
    for k in range(NBLOCKS):
        out.append("set_option maxRecDepth 100000 in\n"
                   "theorem quad_valid_blk%d : ∀ m < %d, %s := by\n  decide +kernel\n\n"
                   % (k, BLOCK, valid_pred("%d * %d + m" % (BLOCK, k))))
    out.append("theorem quad_valid_blocks : ∀ k < %d, ∀ m < %d, %s := by\n"
               "  intro k hk m hm\n  rcases (show %s by omega) with %s\n"
               % (NBLOCKS, BLOCK, valid_pred("%d * k + m" % BLOCK), BLOCK_CASES, BLOCK_PATS))
    for k in range(NBLOCKS):
        out.append("  · exact quad_valid_blk%d m hm\n" % k)
    out.append("\n/-- The representative `quad n` is a determinant-one matrix in normal form, for `n < 12180`. -/\n"
               "theorem quad_valid : ∀ n < %d, %s :=\n  all_of_blocks quad_valid_blocks\n\n"
               % (NSL, valid_pred("n")))
    for k in range(NBLOCKS):
        e = "%d * %d + m" % (BLOCK, k)
        out.append("set_option maxRecDepth 100000 in\n"
                   "theorem enc_of_quad_blk%d : ∀ m < %d, %s := by\n  decide +kernel\n\n"
                   % (k, BLOCK, enc_pred(e, e)))
    out.append("theorem enc_of_quad_blocks : ∀ k < %d, ∀ m < %d, %s := by\n"
               "  intro k hk m hm\n  rcases (show %s by omega) with %s\n"
               % (NBLOCKS, BLOCK, enc_pred("%d * k + m" % BLOCK, "%d * k + m" % BLOCK), BLOCK_CASES, BLOCK_PATS))
    for k in range(NBLOCKS):
        out.append("  · exact enc_of_quad_blk%d m hm\n" % k)
    out.append("\n/-- The class with index `n` is encoded back to `n`, for `n < 12180`. -/\n"
               "theorem enc_of_quad : ∀ n < %d, %s :=\n  all_of_blocks enc_of_quad_blocks\n\n"
               % (NSL, enc_pred("n", "n")))
    return "".join(out)


def main():
    sol, outdir = sys.argv[1], sys.argv[2]
    S = parse_sol(sol)
    check_group_numbering()
    digits = find_words(S)
    verify(S, digits)
    os.makedirs(outdir, exist_ok=True)
    with open(os.path.join(outdir, "codes.json"), "w") as f:
        json.dump({"S": S, "A": digits["A"], "B": digits["B"]}, f)
    lean = os.path.join(outdir, "lean")
    emit_lean(digits, lean)
    with open(os.path.join(lean, "Gens.lean"), "w") as f:
        f.write(gens_text(S))
    if len(sys.argv) > 3:
        with open(os.path.join(lean, "PSL29.lean"), "w") as f:
            f.write(psl29_text(sys.argv[3]))
    print("S =", S)
    print("verified A and B words for all", N, "elements")


if __name__ == "__main__":
    main()
