#!/usr/bin/env python3
"""Covering certificates for the (6,9) Haar record: G = SL(2,23) x Z_5 (order 60720), S from
research/frontier/sols/d6D9_sl_23_5_s401.txt.

Numbering (must match lean/BipartiteDD/Haar/SL23.lean and SL23Z5.lean):
  SL(2,23) element [[a,b],[c,d]] has index enc(a,b,c,d) in [0, 12144):
    c = 0:  (a-1)*23 + b                      (a in 1..22, b in 0..22; 506 elements)
    c != 0: 506 + ((c-1)*23 + a)*23 + d        (c in 1..22; 11638 elements)
  G element (M, z) has index n = 5*enc(M) + z.

Certificates. For every g in G, two words of four pairs (digits d0..d7 in 0..5, indices into S):
  A-word: g = P(d0,d1) P(d2,d3) P(d4,d5) P(d6,d7),   P(x,y) = s_x^-1 s_y
  B-word: g = Q(d0,d1) Q(d2,d3) Q(d4,d5) Q(d6,d7),   Q(x,y) = s_x s_y^-1
The code is sum_k d_k 6^k (< 6^8 < 2^21). Entry n of the A (resp. B) table is the code of the A (resp. B) word
of the element with index n. Every word is re-checked here by direct multiplication.

Usage: python3 gen_d6D9.py SOL.txt OUTDIR
writes OUTDIR/codes.json and OUTDIR/lean/Stage{00..11}.lean, OUTDIR/lean/Cover.lean.
The Lean files are copied to lean/BipartiteDD/Haar/D6D9/ by hand (the generator does not touch the repo).
"""
import json
import os
import re
import sys

import numpy as np

Q = 23
NZ = 5
NSL = Q * (Q * Q - 1)  # 12144
N = NSL * NZ  # 60720
NS = 6
STAGES = 12
STAGE = N // STAGES  # 5060
assert STAGE * STAGES == N


def inv_mod(x):
    return pow(int(x), Q - 2, Q)


def enc_sl(a, b, c, d):
    if c == 0:
        return (a - 1) * Q + b
    return 506 + ((c - 1) * Q + a) * Q + d


def quad_sl(m):
    if m < 506:
        a = m // Q + 1
        return (a, m % Q, 0, inv_mod(a))
    mm = m - 506
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
    assert head[2] == "sl" and int(head[3]) == Q and int(head[5]) == NZ and int(head[7]) == N, head
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
    """For each index n, the A and B digit tuples (d0..d7) of its covering words."""
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
        # left half: two-pair products X, with X[elt index] = digits (x1,y1,x2,y2)
        table = {}
        for (x1, y1), p1 in P.items():
            for (x2, y2), p2 in P.items():
                table.setdefault(enc_g(*mul(p1, p2)), (x1, y1, x2, y2))
        mask = np.zeros(N, dtype=bool)
        mask[list(table.keys())] = True
        # right half: two-pair products Y; then g = X Y with X = g Y^-1 in the table
        ylist = {}
        for (x3, y3) in P:
            for (x4, y4) in P:
                yel = mul(P[(x3, y3)], P[(x4, y4)])
                ylist.setdefault(enc_g(*yel), (yel, (x3, y3, x4, y4)))
        words = {}
        for _, (yel, ydig) in ylist.items():
            ya, yb, yc, yd, yz = inv(yel)
            Xa = (A * ya + B * yc) % Q
            Xb = (A * yb + B * yd) % Q
            Xc = (C * ya + D * yc) % Q
            Xd = (C * yb + D * yd) % Q
            Xz = (Z + yz) % NZ
            Xn = NZ * np.where(Xc == 0, (Xa - 1) * Q + Xb, 506 + ((Xc - 1) * Q + Xa) * Q + Xd) + Xz
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
    for k in range(0, 8, 2):
        x, y = digs[k], digs[k + 1]
        if side == "A":
            el = mul(el, mul(inv(S[x]), S[y]))
        else:
            el = mul(el, mul(S[x], inv(S[y])))
    return el


def code_of(digs):
    return sum(d * 6 ** k for k, d in enumerate(digs))


def verify(S, digits):
    for side in ("A", "B"):
        for n in range(N):
            assert word_value(S, digits[side][n], side) == quad_g(n), (side, n)


LEAN_STAGE = """import BipartiteDD.Haar.D6D9.Check

/-! Covering certificates, stage {k} of 12: the indices `{lo} ≤ n < {hi}` of the (6,9) record on
`SL(2, 23) × Z_5`. Generated by research/lean-haarD/gen_d6D9.py. Do not edit by hand.

`stageA{k}` (resp. `stageB{k}`) packs the base-6 codes of the A-words (resp. B-words) of the elements with indices
`{lo} ≤ n < {hi}`: the code of index `{lo} + i` is `codeAt stageA{k} i`, 21 bits each. -/

namespace BipartiteDD.Haar.D6D9

def stageA{k} : ℕ := {a}

def stageB{k} : ℕ := {b}

set_option maxRecDepth 100000 in
theorem certA{k} : chkA {lo} {len} stageA{k} = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem certB{k} : chkB {lo} {len} stageB{k} = true := by decide +kernel

end BipartiteDD.Haar.D6D9
"""

COVER = """import BipartiteDD.Haar.D6D9.Check
{imports}

/-! Covering hypotheses of the (6,9) record: every element of `SL(2, 23) × Z_5` is an A-word and a B-word
in the connection set `SS`, by the kernel-checked certificates of the stage modules. Generated by
research/lean-haarD/gen_d6D9.py. Do not edit by hand. -/

namespace BipartiteDD.Haar.D6D9

open BipartiteDD.Haar.SL23Z5

/-- Every index `n < 60720` has an A-code. -/
theorem exA (n : ℕ) (hn : n < 60720) : ∃ c, okA c n = true := by
  obtain ⟨k, hk⟩ : ∃ k, n / {stage} = k := ⟨_, rfl⟩
  have hk12 : k < {stages} := by omega
  interval_cases k
{casesA}

/-- Every index `n < 60720` has a B-code. -/
theorem exB (n : ℕ) (hn : n < 60720) : ∃ c, okB c n = true := by
  obtain ⟨k, hk⟩ : ∃ k, n / {stage} = k := ⟨_, rfl⟩
  have hk12 : k < {stages} := by omega
  interval_cases k
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

end BipartiteDD.Haar.D6D9
"""


def cover_text():
    imports = "\n".join("import BipartiteDD.Haar.D6D9.Stage%02d" % k for k in range(STAGES))
    cases = {}
    for side, ok in (("A", "okA"), ("B", "okB")):
        lines = []
        for k in range(STAGES):
            lines.append("  · exact stageEx%s %d %d stage%s%02d cert%s%02d n (by omega) (by omega)"
                         % (side, k * STAGE, STAGE, side, k, side, k))
        cases[side] = "\n".join(lines)
    text = COVER
    text = text.replace("{imports}", imports)
    text = text.replace("{stage}", str(STAGE))
    text = text.replace("{stages}", str(STAGES))
    text = text.replace("{casesA}", cases["A"])
    text = text.replace("{casesB}", cases["B"])
    return text


def pack(codes):
    v = 0
    for i, c in enumerate(codes):
        assert 0 <= c < 2 ** 21
        v |= c << (21 * i)
    return v


def emit_lean(digits, outdir):
    os.makedirs(outdir, exist_ok=True)
    for k in range(STAGES):
        lo = k * STAGE
        hi = lo + STAGE
        ca = [code_of(digits["A"][n]) for n in range(lo, hi)]
        cb = [code_of(digits["B"][n]) for n in range(lo, hi)]
        text = LEAN_STAGE.format(k="%02d" % k, lo=lo, hi=hi, len=STAGE,
                                 a="0x%x" % pack(ca), b="0x%x" % pack(cb))
        with open(os.path.join(outdir, "Stage%02d.lean" % k), "w") as f:
            f.write(text)
    with open(os.path.join(outdir, "Cover.lean"), "w") as f:
        f.write(cover_text())


def main():
    sol, outdir = sys.argv[1], sys.argv[2]
    S = parse_sol(sol)
    check_group_numbering()
    digits = find_words(S)
    verify(S, digits)
    os.makedirs(outdir, exist_ok=True)
    with open(os.path.join(outdir, "codes.json"), "w") as f:
        json.dump({"S": S, "A": digits["A"], "B": digits["B"]}, f)
    emit_lean(digits, os.path.join(outdir, "lean"))
    print("S =", S)
    print("verified A and B words for all", N, "elements")


if __name__ == "__main__":
    main()
