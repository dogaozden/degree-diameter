#!/usr/bin/env python3
"""Covering certificates for the (6,10) record: G = PGL(2,37) x Z_5 (order 253080), S from
research/frontier/sols/d6D10_pgl_37_5_s401.txt.

Cover (one condition, even D = 10, see lean/BipartiteDD/Haar/Diam10.lean): every g in G is
  x1 (x2^-1) x3 (x4^-1) x5 (x6^-1) x7 (x8^-1) x9      with all xi in S.
Letters: digit d_k (0..5) of the code c = sum d_k 6^k selects s_{d_k} of S; odd positions are inverted.
The PGL part is the Nat matrix product mod 37 (inverse = adjugate, projectively), the Z_5 part is additive
(inverse = negation, so odd positions contribute -z).

Numbering (must match lean/BipartiteDD/Haar/PGL37.lean): class (a,b,c,d) with a = 1 has
  n = (c*37 + b)*36 + ((d - b c - 1) mod 37)            (c*37 + b < 1369)
class with a = 0, c = 1 has n = 49284 + (b - 1)*37 + d.  G element (M, z) has index 5*enc(M) + z.

Usage: python3 gen_d6D10.py SOL.txt OUTDIR
Writes OUTDIR/Check.lean and OUTDIR/Stage00..49.lean (for lean/BipartiteDD/Haar/D6D10/).
Every word is re-checked with the exact Lean formulas (normN(prodN Ls) = quadN(n/5), zW = n%5).
"""
import os
import re
import sys

import numpy as np

P = 37
NZ = 5
NPGL = 50616
N = NPGL * NZ  # 253080
NS = 6
DIG = 9
STAGE = 5624  # 45 stages: 253080 = 45 * 5624
NSTAGES = N // STAGE
assert NSTAGES * STAGE == N
BITS = 24  # codes < 6^9 < 2^24

INV = [0] + [pow(x, P - 2, P) for x in range(1, P)]
INVARR = np.array(INV, dtype=np.int64)


def parse_sol(path):
    lines = [ln.strip() for ln in open(path) if ln.strip()]
    head = lines[0].split()
    assert head[2] == "pgl" and int(head[3]) == P and int(head[5]) == NZ and int(head[7]) == N, head
    S = []
    for ln in lines[1:]:
        m = re.fullmatch(r"\d+\s+mat\((\d+),(\d+),(\d+),(\d+)\)\s+z=(\d+)", ln)
        assert m, ln
        a, b, c, d, z = map(int, m.groups())
        assert (a * d - b * c) % P != 0, ln
        S.append(((a, b, c, d), z))
    assert len(S) == NS and len(set(S)) == NS, S
    return S


# ---- exact Lean mirrors -------------------------------------------------------------------------------------

def mN(x, y):
    a, b, c, d = x
    e, f, g, h = y
    return ((a * e + b * g) % P, (a * f + b * h) % P, (c * e + d * g) % P, (c * f + d * h) % P)


def adjN(x):
    a, b, c, d = x
    return (d, (P - b) % P, (P - c) % P, a)


def leadN(a, c):
    return c % P if a % P == 0 else a % P


def normN(x):
    a, b, c, d = x
    l = INV[leadN(a, c)]
    return ((l * a) % P, (l * b) % P, (l * c) % P, (l * d) % P)


def quadN(n):
    if n < 49284:
        c = (n // 36) // 37
        b = (n // 36) % 37
        k = n % 36
        return (1, b, c, (b * c + 1 + k) % 37)
    m = n - 49284
    return (0, m // 37 + 1, 1, m % 37)


def prodN(L):
    acc = (1, 0, 0, 1)
    for M in reversed(L):
        acc = mN(M, acc)
    return acc


def zW(digs, zs):
    # (z0 + 4 z1 + z2 + 4 z3 + ... + z8) % 5, with zs[j] the Z_5 exponent of s_j
    tot = 0
    for k, d in enumerate(digs):
        tot += zs[d] if k % 2 == 0 else 4 * zs[d]
    return tot % 5


# ---- the search ---------------------------------------------------------------------------------------------

def enc_vec(a, b, c, d):
    """Vectorised enc of normal forms (a in {0,1}); returns index in [0, NPGL)."""
    k = (d - b * c - 1) % P
    n1 = (c * 37 + b) * 36 + k
    n0 = 49284 + (b - 1) * 37 + d
    return np.where(a == 1, n1, n0)


def norm_vec(a, b, c, d):
    lead = np.where(a % P == 0, c % P, a % P)
    l = INVARR[lead]
    return (l * a) % P, (l * b) % P, (l * c) % P, (l * d) % P


def mul_vec(x, y):
    a, b, c, d = x
    e, f, g, h = y
    return ((a * e + b * g) % P, (a * f + b * h) % P, (c * e + d * g) % P, (c * f + d * h) % P)


def find_codes(S):
    sm = [s[0] for s in S]
    zs = [s[1] for s in S]
    # all normal forms of PGL and their indices
    pn = [quadN(p) for p in range(NPGL)]
    A = np.array([q[0] for q in pn], dtype=np.int64)
    B = np.array([q[1] for q in pn], dtype=np.int64)
    C = np.array([q[2] for q in pn], dtype=np.int64)
    D = np.array([q[3] for q in pn], dtype=np.int64)
    assert np.all(enc_vec(A, B, C, D) == np.arange(NPGL))
    # left half: letters 0..4 = s0 s1^-1 s2 s3^-1 s4 ; right half letters 5..8 = s5^-1 s6 s7^-1 s8
    def letter(j, k):
        m = sm[j]
        return m if k % 2 == 0 else adjN(m)

    Lcode = {}
    keyL = np.full(NPGL * NZ, -1, dtype=np.int64)
    codeLarr = np.full(NPGL * NZ, -1, dtype=np.int64)
    for code in range(6 ** 5):
        digs = [(code // 6 ** k) % 6 for k in range(5)]
        M = prodN([letter(digs[k], k) for k in range(5)])
        Mn = normN(M)
        idx = int(enc_vec(np.array(Mn[0]), np.array(Mn[1]), np.array(Mn[2]), np.array(Mn[3])))
        z = (sum(zs[digs[k]] if k % 2 == 0 else -zs[digs[k]] for k in range(5))) % NZ
        key = idx * NZ + z
        if keyL[key] < 0:
            keyL[key] = 1
            codeLarr[key] = code
    assert (keyL >= 0).sum() > 0
    hasL = keyL >= 0
    print("left keys:", int(hasL.sum()), flush=True)

    nidx = np.arange(N)
    pidx_of_n = nidx // NZ
    zof_n = nidx % NZ
    found = np.full(N, -1, dtype=np.int64)
    Ap, Bp, Cp, Dp = A, B, C, D
    for code_r in range(6 ** 4):
        digsR = [(code_r // 6 ** k) % 6 for k in range(4)]  # positions 5..8 -> k = 0..3 here
        digs_abs = [0] * 5 + digsR
        R = prodN([letter(digs_abs[k], k) if False else None for k in []]) if False else None
        Rm = (1, 0, 0, 1)
        zR = 0
        for i in range(4):
            k = 5 + i
            j = digsR[i]
            mat = sm[j] if k % 2 == 0 else adjN(sm[j])
            Rm = mN(Rm, mat)
            zR += zs[j] if k % 2 == 0 else -zs[j]
        zR %= NZ
        # g R^-1 = g * adj(R) (projective), for every PGL element p
        Rinv = adjN(Rm)
        Mx = mul_vec((Ap, Bp, Cp, Dp), Rinv)
        Mn = norm_vec(*Mx)
        pidxM = enc_vec(Mn[0], Mn[1], Mn[2], Mn[3])
        keys = pidxM[pidx_of_n] * NZ + ((zof_n - zR) % NZ)
        hit = hasL[keys] & (found < 0)
        if hit.any():
            found[hit] = codeLarr[keys[hit]] + code_r * 6 ** 5 * 0 + sum(digsR[i] * 6 ** (5 + i) for i in range(4))
        if (found >= 0).all():
            break
    assert (found >= 0).all(), int((found < 0).sum())
    return found


def digits(code):
    return [(code // 6 ** k) % 6 for k in range(DIG)]


def verify(S, codes):
    sm = [s[0] for s in S]
    zs = [s[1] for s in S]
    for n in range(N):
        digs = digits(int(codes[n]))
        Ls = [sm[digs[k]] if k % 2 == 0 else adjN(sm[digs[k]]) for k in range(DIG)]
        w = normN(prodN(Ls))
        assert w == quadN(n // NZ), ("PGL", n)
        assert zW(digs, zs) == n % NZ, ("Z", n)


LEAN_CHECK = """import BipartiteDD.Haar.PGL37Nat

/-! The kernel-checkable certificate of the (6,10) record on `PGL(2, 37) × Z_5` (order 253080).

The connection set `S` is the six elements `sTab[j]` with Z_5 exponents `zTab[j]`, from
`research/frontier/sols/d6D10_pgl_37_5_s401.txt`. The code `c = Σ dₖ 6ᵏ` (nine digits) gives the word
`x₁ x₂⁻¹ x₃ x₄⁻¹ x₅ x₆⁻¹ x₇ x₈⁻¹ x₉` with `xₖ = s_{dₖ}`. In `PGL(2, 37)` the inverse is the adjugate, and
`prodN` is the Nat product mod 37 (`PGL37Nat`). `okC c n` says that the word of `c` is the element with
index `n` (`n / 5` in `PGL(2, 37)`, `n % 5` in `Z_5`). The tables are generated by
research/lean-haarD/gen_d6D10.py; do not edit by hand. -/

namespace BipartiteDD.Haar.D6D10

open BipartiteDD.Haar.PGL37

/-- The matrices of the connection set, as Nat quadruples. -/
def sTab : List (ℕ × ℕ × ℕ × ℕ) := [@@S@@]

/-- The `Z_5` exponents of the connection set. -/
def zTab : List ℕ := [@@Z@@]

/-- The `j`-th matrix of `S`, for `j < 6`. -/
def sN (j : ℕ) : ℕ × ℕ × ℕ × ℕ := sTab.getD j (1, 0, 0, 1)

/-- The `Z_5` exponent of the `j`-th element of `S`. -/
def zN (j : ℕ) : ℕ := zTab.getD j 0

/-- The digit `k` of the code `c`, in base 6. -/
def dig (c k : ℕ) : ℕ := c / 6 ^ k % 6

/-- The nine letters of the word of `c`: the `sₖ` at the even positions, their adjugates at the odd ones. -/
def Ls (c : ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  [sN (dig c 0), adjN (sN (dig c 1)), sN (dig c 2), adjN (sN (dig c 3)), sN (dig c 4),
    adjN (sN (dig c 5)), sN (dig c 6), adjN (sN (dig c 7)), sN (dig c 8)]

/-- The `Z_5` part of the word of `c`: `z₀ - z₁ + z₂ - ⋯ + z₈`, written with `-z ≡ 4 z` mod 5. -/
def zW (c : ℕ) : ℕ :=
  (zN (dig c 0) + 4 * zN (dig c 1) + zN (dig c 2) + 4 * zN (dig c 3) + zN (dig c 4) + 4 * zN (dig c 5)
    + zN (dig c 6) + 4 * zN (dig c 7) + zN (dig c 8)) % 5

/-- The code `c` gives the element with index `n` of `PGL(2, 37) × Z_5`. -/
def okC (c n : ℕ) : Bool :=
  decide (normN (prodN (Ls c)) = quadN (n / 5)) && decide (zW c = n % 5)

/-- The code in position `i` of a stage table `C`: 24 bits each. -/
def codeAt (C i : ℕ) : ℕ := (C >>> (24 * i)) % 16777216

/-- `chkC base len C`: the codes of the stage table `C` certify the indices `base … base + len - 1`. -/
def chkC (base len C : ℕ) : Bool :=
  (List.range len).all (fun i => okC (codeAt C i) (base + i))

theorem okC_ex (base len C : ℕ) (h : chkC base len C = true) (n : ℕ) (hn : base ≤ n) (hn' : n < base + len) :
    ∃ c, okC c n = true := by
  refine ⟨codeAt C (n - base), ?_⟩
  have := List.all_eq_true.mp h (n - base) (List.mem_range.mpr (by omega))
  rwa [show base + (n - base) = n by omega] at this

theorem okC_spec {c n : ℕ} (h : okC c n = true) :
    normN (prodN (Ls c)) = quadN (n / 5) ∧ zW c = n % 5 := by
  unfold okC at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

end BipartiteDD.Haar.D6D10
"""


def lean_check_module(S):
    sm = [s[0] for s in S]
    zs = [s[1] for s in S]
    sTab = ", ".join("(%d, %d, %d, %d)" % m for m in sm)
    zTab = ", ".join(str(z) for z in zs)
    return LEAN_CHECK.replace("@@S@@", sTab).replace("@@Z@@", zTab)


def stage_module(k, codes):
    lo = k * STAGE
    packed = 0
    for i in range(STAGE):
        c = codes[lo + i]
        assert 0 <= c < 2 ** BITS
        packed |= int(c) << (BITS * i)
    return f"""import BipartiteDD.Haar.D6D10.Check

/-! Certificates for the (6,10) record, stage {k:02d} of {NSTAGES}: the indices `{lo} ≤ n < {lo + STAGE}`.
Generated by research/lean-haarD/gen_d6D10.py. Do not edit by hand. -/

namespace BipartiteDD.Haar.D6D10

def stageC{k:02d} : ℕ := 0x{packed:x}

set_option maxRecDepth 100000 in
theorem certC{k:02d} : chkC {lo} {STAGE} stageC{k:02d} = true := by decide +kernel

end BipartiteDD.Haar.D6D10
"""


def cover_module():
    imports = "\n".join("import BipartiteDD.Haar.D6D10.Stage%02d" % k for k in range(NSTAGES))
    ors = " ∨ ".join("k = %d" % k for k in range(NSTAGES))
    alts = " | ".join("h%d" % k for k in range(NSTAGES))
    cases = "\n".join(
        "  · exact okC_ex %d %d stageC%02d certC%02d n (by omega) (by omega)" % (k * STAGE, STAGE, k, k)
        for k in range(NSTAGES))
    return f"""import BipartiteDD.Haar.D6D10.Check
{imports}

/-! Every index `n < 253080` has a certificate code, by the stage checks. Generated by
research/lean-haarD/gen_d6D10.py. Do not edit by hand. -/

namespace BipartiteDD.Haar.D6D10

theorem exC (n : ℕ) (hn : n < 253080) : ∃ c, okC c n = true := by
  obtain ⟨k, hk⟩ : ∃ k, n / {STAGE} = k := ⟨_, rfl⟩
  have hk12 : k < {NSTAGES} := by omega
  rcases (show {ors} by omega) with {alts}
{cases}

end BipartiteDD.Haar.D6D10
"""


def main():
    sol, outdir = sys.argv[1], sys.argv[2]
    S = parse_sol(sol)
    codes = find_codes(S)
    verify(S, codes)
    os.makedirs(outdir, exist_ok=True)
    with open(os.path.join(outdir, "Check.lean"), "w") as f:
        f.write(lean_check_module(S))
    for k in range(NSTAGES):
        with open(os.path.join(outdir, "Stage%02d.lean" % k), "w") as f:
            f.write(stage_module(k, codes))
    with open(os.path.join(outdir, "Cover.lean"), "w") as f:
        f.write(cover_module())
    print("ok: all", N, "elements certified; stages", NSTAGES, flush=True)


if __name__ == "__main__":
    main()
