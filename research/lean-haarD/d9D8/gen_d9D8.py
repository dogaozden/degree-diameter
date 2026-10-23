#!/usr/bin/env python3
"""Certificate generator for the Delta9*D8 record: the Haar graph of G = PSL(2,23) x Z41 (order 248952), |S| = 9.

The connection set is read from research/frontier/sols/d9D8_psl_23_41_s301.txt. Diameter 8 is the even case
`haar_ediam_le_even` with n = 3: every x in G is s * y with s in S and y = p1^-1 p2 p3^-1 p4 p5^-1 p6 (p_i in S).
So every index n has a code c = d0 + 9 d1 + ... + 9^6 d6 (base 9) with

    wE c = S[d0] * (S[d1]^-1 S[d2]) * (S[d3]^-1 S[d4]) * (S[d5]^-1 S[d6]),

and the index of x is 41 * enc(psl part) + z (see Lean `D9D8.Base`). The codes are packed 23 bits each into stage
constants, `L` codes per stage, and written to lean/BipartiteDD/Haar/D9D8/:
  Gens.lean        the nine generators `sGl`
  Stage<kk>.lean   stage kk: the codes of the indices [base, base + len), checked by `decide +kernel`
  Cover.lean       `exE`: every index has a code (dispatch on the stage)

Before writing, this script re-multiplies every word in the group law of the Lean module (same normal form,
same numbering) and checks that every element of G has a code. Lean re-checks everything by kernel computation.

Usage: python3 gen_d9D8.py [SOLFILE] [LEAN_DIR]
"""
import os
import re
import sys
from itertools import product

P = 23            # the prime
HALF = 11         # (P - 1) / 2: the representative window of posB
NPSL = 6072       # |PSL(2,23)| = 23 (23^2 - 1) / 2
NZ = 41           # Z41
N = NPSL * NZ     # 248952 = |G|, vertices per side
K = 9             # |S|
L = 4446          # indices per stage
BITS = 23         # bits per code; 9^7 = 4782969 < 2^23

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
SOL = sys.argv[1] if len(sys.argv) > 1 else os.path.join(ROOT, "research/frontier/sols/d9D8_psl_23_41_s301.txt")
OUT = sys.argv[2] if len(sys.argv) > 2 else os.path.join(ROOT, "lean/BipartiteDD/Haar/D9D8")


# ---------------------------------------------------------------- PSL(2,23), normal form as in PSL23.lean
def posB(a, c):
    return (a <= HALF) if c == 0 else (c <= HALF)


def canon(a, b, c, d):
    a, b, c, d = a % P, b % P, c % P, d % P
    if posB(a, c):
        return (a, b, c, d)
    return ((-a) % P, (-b) % P, (-c) % P, (-d) % P)


def mul(g, h):
    a, b, c, d = g
    e, f, p, q = h
    return canon(a * e + b * p, a * f + b * q, c * e + d * p, c * f + d * q)


def inv(g):
    a, b, c, d = g
    return canon(d, -b, -c, a)


def invP(x):
    return pow(x, P - 2, P)


def enc(g):
    a, b, c, d = g
    if c == 0:
        return (a - 1) * P + b
    return 253 + ((c - 1) * P + a) * P + d


def quad(n):
    if n < 253:
        a = n // P + 1
        return (a, n % P, 0, invP(a))
    m = n - 253
    c = m // 529 + 1
    a = (m // P) % P
    d = m % P
    b = ((a * d - 1) * invP(c)) % P
    return (a, b, c, d)


def det1(g):
    a, b, c, d = g
    return (a * d - b * c) % P == 1


# self-check of the numbering: enc is a bijection quad : [0, 6072) -> PSL(2,23)
for n in range(NPSL):
    q = quad(n)
    assert det1(q) and posB(q[0], q[2]), n
    assert enc(q) == n, n
assert len({quad(n) for n in range(NPSL)}) == NPSL


# ---------------------------------------------------------------- G = PSL(2,23) x Z41; elements (psl, z)
def gmul(g, h):
    return (mul(g[0], h[0]), (g[1] + h[1]) % NZ)


def ginv(g):
    return (inv(g[0]), (-g[1]) % NZ)


def gidx(g):
    return enc(g[0]) * NZ + g[1]


def read_sol(path):
    with open(path) as f:
        lines = [ln.strip() for ln in f if ln.strip()]
    hdr = lines[0].split()
    assert hdr[0] == str(K) and hdr[1] == "8" and hdr[2] == "psl" and hdr[3] == "23", hdr
    assert hdr[5] == str(NZ) and int(hdr[7]) == N, hdr
    gens = []
    for ln in lines[1:]:
        m = re.match(r"\d+\s+mat\((-?\d+),(-?\d+),(-?\d+),(-?\d+)\)\s+z=(\d+)$", ln)
        assert m, ln
        a, b, c, d = map(int, m.group(1, 2, 3, 4))
        assert (a * d - b * c) % P == 1, ln
        gens.append((canon(a, b, c, d), int(m.group(5)) % NZ))
    assert len(gens) == K
    assert len(set(gens)) == K, "generators not distinct"
    return gens


S = read_sol(SOL)
Q = [[gmul(ginv(S[i]), S[j]) for j in range(K)] for i in range(K)]   # Q[i][j] = S_i^-1 S_j

# ---------------------------------------------------------------- covering codes
first = [-1] * N
for ds in product(range(K), repeat=6):
    d1, d2, d3, d4, d5, d6 = ds
    W = gmul(gmul(Q[d1][d2], Q[d3][d4]), Q[d5][d6])          # S_d1^-1 S_d2 S_d3^-1 S_d4 S_d5^-1 S_d6
    # code c = d0 + 9 d1 + 81 d2 + ... + 9^6 d6: the digit d_k has weight 9^k
    base = 9 * (d1 + 9 * (d2 + 9 * (d3 + 9 * (d4 + 9 * (d5 + 9 * d6)))))
    for d0 in range(K):
        g = gmul(S[d0], W)
        i = gidx(g)
        if first[i] < 0:
            first[i] = base + d0

missing = [i for i in range(N) if first[i] < 0]
if missing:
    print(f"NOT COVERED: {len(missing)} indices, e.g. {missing[:5]}")
    sys.exit(1)
print(f"all {N} indices covered by 7-letter words (9^7 = {9**7} codes)")

# independent check of a sample of codes against the direct word in the group law
def wE(c):
    d = [(c // 9 ** k) % 9 for k in range(7)]
    g = S[d[0]]
    for k in range(1, 7, 2):
        g = gmul(g, gmul(ginv(S[d[k]]), S[d[k + 1]]))
    return g


for n in list(range(0, N, 997)) + [N - 1]:
    c = first[n]
    assert c >= 0
    assert gidx(wE(c)) == n, (n, c)
print("sampled codes re-multiplied in the group law: OK")

# ---------------------------------------------------------------- Lean output
os.makedirs(OUT, exist_ok=True)
HDR = "/- Generated by research/lean-haarD/d9D8/gen_d9D8.py. Do not edit by hand. -/\n"


def lean_gen(g):
    (a, b, c, d), z = g
    return f"(⟨{a}, {b}, {c}, {d}, by decide, by decide⟩, Multiplicative.ofAdd ({z} : ZMod 41))"


with open(os.path.join(OUT, "Gens.lean"), "w") as f:
    f.write(HDR)
    f.write("import BipartiteDD.Haar.D9D8.Base\n\n")
    f.write("/-! The nine generators `S` of the Δ9·D8 record (`d9D8_psl_23_41_s301`), as elements of\n")
    f.write("`PSL(2,23) × ZMod 41` in the normal form of `PSL23`. -/\n\n")
    f.write("namespace BipartiteDD.Haar.D9D8\n\nopen BipartiteDD.Haar.PSL23\n\n")
    f.write("/-- The generators, indexed `0 … 8`. -/\n")
    f.write("def sGl : List G :=\n  [" + ",\n    ".join(lean_gen(g) for g in S) + "]\n\n")
    f.write("end BipartiteDD.Haar.D9D8\n")

NST = (N + L - 1) // L
for k in range(NST):
    base = k * L
    ln = min(L, N - base)
    C = 0
    for i in range(ln):
        C |= first[base + i] << (BITS * i)
    with open(os.path.join(OUT, f"Stage{k:02d}.lean"), "w") as f:
        f.write(HDR)
        f.write("import BipartiteDD.Haar.D9D8.Check\n\n")
        f.write(f"/-! Covering certificates, stage {k:02d} of {NST}: the indices `{base} ≤ n < {base + ln}` of the\n")
        f.write("Δ9·D8 record on `PSL(2, 23) × Z41`. `stage{:02d}` packs the base-9 codes of these indices, {} bits\n".format(k, BITS))
        f.write("each: the code of index `base + i` is `codeAt stage{:02d} i`. -/\n\n".format(k))
        f.write("namespace BipartiteDD.Haar.D9D8\n\n")
        f.write(f"def stage{k:02d} : ℕ := 0x{C:x}\n\n")
        f.write("set_option maxRecDepth 100000 in\n")
        f.write(f"theorem cert{k:02d} : chkStage {base} {ln} stage{k:02d} = true := by decide +kernel\n\n")
        f.write("end BipartiteDD.Haar.D9D8\n")

with open(os.path.join(OUT, "Cover.lean"), "w") as f:
    f.write(HDR)
    f.write("import BipartiteDD.Haar.D9D8.Check\n")
    for k in range(NST):
        f.write(f"import BipartiteDD.Haar.D9D8.Stage{k:02d}\n")
    f.write("\n/-! Every index `n < 248952` has a code: the stage certificates `cert00 … cert{:02d}`. -/\n\n".format(NST - 1))
    f.write("namespace BipartiteDD.Haar.D9D8\n\n")
    f.write("theorem exE (n : ℕ) (hn : n < 248952) : ∃ c, chkE n c = true := by\n")
    f.write("  rcases (show " + " ∨ ".join(f"n / {L} = {k}" for k in range(NST)) + " by omega) with ")
    f.write(" | ".join(f"h{k}" for k in range(NST)) + "\n")
    for k in range(NST):
        base = k * L
        ln = min(L, N - base)
        f.write(f"  · exact stageEx {base} {ln} stage{k:02d} cert{k:02d} n (by omega) (by omega)\n")
    f.write("\nend BipartiteDD.Haar.D9D8\n")

print(f"wrote {NST} stages of {L} codes (last {N - (NST - 1) * L}) to {OUT}")
