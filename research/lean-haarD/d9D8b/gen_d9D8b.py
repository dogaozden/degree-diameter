#!/usr/bin/env python3
"""Certificate generator for the Delta9*D8 record of 511,056 vertices: the Haar graph of G = SL(2,27) x Z13.

|G| = 19656 * 13 = 255528, so the record has 2 |G| = 511056 vertices. The connection set is read from
research/frontier/sols/d9D8_sl_27_13_orb3_s1.txt (poly x^3+2x+1). Diameter 8 is the even case `haar_ediam_le_even`
with n = 3: every x in G is s * y with s in S and y = p1^-1 p2 p3^-1 p4 p5^-1 p6 (p_i in S). So every index n has a
code c = d0 + 9 d1 + ... + 9^6 d6 (base 9) with

    wE c = S[d0] * (S[d1]^-1 S[d2]) * (S[d3]^-1 S[d4]) * (S[d5]^-1 S[d6]),

and the index of (g, z) is 13 * enc(matrix) + z (see Lean `D9D8b.Base`). Codes are packed 23 bits each into stage
constants, L codes per stage, and written to lean/BipartiteDD/Haar/D9D8b/:
  Gens.lean        the nine generators `sGl`
  Stage<kk>.lean   stage kk: the codes of the indices [base, base + len), checked by `decide +kernel`
  Cover.lean       `exE`: every index has a code (dispatch on the stage)

Before writing, this script checks the numbering (quad is a bijection onto SL(2,27) with det 1), re-multiplies every
sampled word in the group law of the Lean module, and checks that every element of G has a code.

Usage: python3 gen_d9D8b.py [SOLFILE] [LEAN_DIR]
"""
import os
import re
import sys
from itertools import product

NSL = 19656          # |SL(2,27)| = 27 (27^2 - 1) = 27 * 728 = 19656
NZ = 13              # Z13
N = NSL * NZ         # 255528 = |G|, vertices per side
K = 9                # |S|
L = 4446             # indices per stage
BITS = 23            # bits per code; 9^7 = 4782969 < 2^23
NV = 2 * N           # 511056 vertices in total

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
SOL = sys.argv[1] if len(sys.argv) > 1 else os.path.join(ROOT, "research/frontier/sols/d9D8_sl_27_13_orb3_s1.txt")
OUT = sys.argv[2] if len(sys.argv) > 2 else os.path.join(ROOT, "lean/BipartiteDD/Haar/D9D8b")

# ---------------------------------------------------------------- GF(27) = GF(3)[x]/(x^3+2x+1)
# element n = c0 + 3 c1 + 9 c2 stands for c0 + c1 x + c2 x^2; x^3 = x + 2
def fadd(a, b):
    return (a % 3 + b % 3) % 3 + 3 * ((a // 3 % 3 + b // 3 % 3) % 3) + 9 * ((a // 9 + b // 9) % 3)


def fmul(a, b):
    a0, a1, a2 = a % 3, a // 3 % 3, a // 9
    b0, b1, b2 = b % 3, b // 3 % 3, b // 9
    c0 = a0 * b0
    c1 = a0 * b1 + a1 * b0
    c2 = a0 * b2 + a1 * b1 + a2 * b0
    c3 = a1 * b2 + a2 * b1
    c4 = a2 * b2
    return (c0 + 2 * c3) % 3 + 3 * ((c1 + c3 + 2 * c4) % 3) + 9 * ((c2 + c4) % 3)


def fneg(a):
    return (3 - a % 3) % 3 + 3 * ((3 - a // 3 % 3) % 3) + 9 * ((3 - a // 9) % 3)


INV = [0] * 27
for _x in range(1, 27):
    INV[_x] = next(_y for _y in range(27) if fmul(_x, _y) == 1)
assert INV[1:] == [1, 2, 19, 21, 24, 11, 12, 15, 25, 23, 6, 7, 22, 18, 8, 20, 26, 14, 3, 16, 4, 13, 10, 5, 9, 17]
assert all(fmul(a, b) == fmul(b, a) for a in range(27) for b in range(27))
assert all(fmul(a, fadd(b, c)) == fadd(fmul(a, b), fmul(a, c)) for a in range(27) for b in range(27) for c in range(27))
assert all(fmul(a, fmul(b, c)) == fmul(fmul(a, b), c) for a in range(27) for b in range(27) for c in range(27))
assert all(fmul(x, INV[x]) == 1 for x in range(1, 27))
assert len({fmul(x, y) for x in range(1, 27) for y in range(1, 27)}) == 26  # no zero divisors (a field)


# ---------------------------------------------------------------- SL(2,27), numbering as in SL2.lean
def enc(g):
    a, b, c, d = g
    if c == 0:
        return (a - 1) * 27 + b
    return 702 + ((c - 1) * 27 + a) * 27 + d


def quad(n):
    if n < 702:
        a = n // 27 + 1
        return (a, n % 27, 0, INV[a])
    m = n - 702
    c = m // 729 + 1
    a = m // 27 % 27
    d = m % 27
    b = fmul(fadd(fmul(a, d), fneg(1)), INV[c])
    return (a, b, c, d)


def det1(g):
    a, b, c, d = g
    return fadd(fmul(a, d), fneg(fmul(b, c))) == 1


for n in range(NSL):
    q = quad(n)
    assert det1(q), n
    assert enc(q) == n, n
assert len({quad(n) for n in range(NSL)}) == NSL


# ---------------------------------------------------------------- G = SL(2,27) x Z13; elements (matrix, z)
def mul(g, h):
    a, b, c, d = g
    e, f, p, q = h
    return (fadd(fmul(a, e), fmul(b, p)), fadd(fmul(a, f), fmul(b, q)),
            fadd(fmul(c, e), fmul(d, p)), fadd(fmul(c, f), fmul(d, q)))


def inv(g):
    a, b, c, d = g
    return (d, fneg(b), fneg(c), a)


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
    assert hdr[0] == str(K) and hdr[1] == "8" and hdr[2] == "sl" and hdr[3] == "27", hdr
    assert hdr[4:7] == ["poly", "x^3+2x+1", "n"] or hdr[4:7] == ["poly", "x^3+2x+1", "n"], hdr
    assert hdr[7] == str(NZ) and int(hdr[9]) == N, hdr
    gens = []
    for ln in lines[1:]:
        m = re.match(r"\d+\s+mat\((\d+),(\d+),(\d+),(\d+)\)\s+z=(\d+)$", ln)
        assert m, ln
        mat = tuple(int(t) for t in m.group(1, 2, 3, 4))
        assert all(0 <= t < 27 for t in mat), ln
        assert det1(mat), ln
        gens.append((mat, int(m.group(5)) % NZ))
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
    base = 9 * (d1 + 9 * (d2 + 9 * (d3 + 9 * (d4 + 9 * (d5 + 9 * d6)))))
    for d0 in range(K):
        i = gidx(gmul(S[d0], W))
        if first[i] < 0:
            first[i] = base + d0

missing = [i for i in range(N) if first[i] < 0]
if missing:
    print(f"NOT COVERED: {len(missing)} indices, e.g. {missing[:5]}")
    sys.exit(1)
print(f"all {N} indices covered by 7-letter words (9^7 = {9**7} codes)")


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
HDR = "/- Generated by research/lean-haarD/d9D8b/gen_d9D8b.py. Do not edit by hand. -/\n"


def lean_gen(g):
    (a, b, c, d), z = g
    # the entries are field elements, numbered by `ofN` (numerals of GF(27) would reduce mod 3)
    return f"(⟨ofN {a}, ofN {b}, ofN {c}, ofN {d}, by decide⟩, Multiplicative.ofAdd ({z} : ZMod 13))"


with open(os.path.join(OUT, "Gens.lean"), "w") as f:
    f.write(HDR)
    f.write("import BipartiteDD.Haar.D9D8b.Base\n\n")
    f.write("/-! The nine generators `S` of the Δ9·D8 record (`d9D8_sl_27_13_orb3_s1`), as elements of\n")
    f.write("`SL(2,27) × ZMod 13` in the normal form of `SL2`. -/\n\n")
    f.write("namespace BipartiteDD.Haar.D9D8b\n\n")
    f.write("/-- The generators, indexed `0 … 8`. -/\n")
    f.write("def sGl : List G :=\n  [" + ",\n    ".join(lean_gen(g) for g in S) + "]\n\n")
    f.write("end BipartiteDD.Haar.D9D8b\n")

NST = (N + L - 1) // L
for k in range(NST):
    base = k * L
    ln = min(L, N - base)
    C = 0
    for i in range(ln):
        C |= first[base + i] << (BITS * i)
    with open(os.path.join(OUT, f"Stage{k:02d}.lean"), "w") as f:
        f.write(HDR)
        f.write("import BipartiteDD.Haar.D9D8b.Check\n\n")
        f.write(f"/-! Covering certificates, stage {k:02d} of {NST}: the indices `{base} ≤ n < {base + ln}` of the\n")
        f.write("Δ9·D8 record on `SL(2, 27) × Z13`. `stage{:02d}` packs the base-9 codes of these indices, {} bits\n".format(k, BITS))
        f.write("each: the code of index `base + i` is `codeAt stage{:02d} i`. -/\n\n".format(k))
        f.write("namespace BipartiteDD.Haar.D9D8b\n\n")
        f.write(f"def stage{k:02d} : ℕ := 0x{C:x}\n\n")
        f.write("set_option maxRecDepth 100000 in\n")
        f.write(f"theorem cert{k:02d} : chkStage {base} {ln} stage{k:02d} = true := by decide +kernel\n\n")
        f.write("end BipartiteDD.Haar.D9D8b\n")

with open(os.path.join(OUT, "Cover.lean"), "w") as f:
    f.write(HDR)
    f.write("import BipartiteDD.Haar.D9D8b.Check\n")
    for k in range(NST):
        f.write(f"import BipartiteDD.Haar.D9D8b.Stage{k:02d}\n")
    f.write("\n/-! Every index `n < {}` has a code: the stage certificates `cert00 … cert{:02d}`. -/\n\n".format(N, NST - 1))
    f.write("namespace BipartiteDD.Haar.D9D8b\n\n")
    f.write(f"theorem exE (n : ℕ) (hn : n < {N}) : ∃ c, chkE n c = true := by\n")
    f.write("  rcases (show " + " ∨ ".join(f"n / {L} = {k}" for k in range(NST)) + " by omega) with ")
    f.write(" | ".join(f"h{k}" for k in range(NST)) + "\n")
    for k in range(NST):
        base = k * L
        ln = min(L, N - base)
        f.write(f"  · exact stageEx {base} {ln} stage{k:02d} cert{k:02d} n (by omega) (by omega)\n")
    f.write("\nend BipartiteDD.Haar.D9D8b\n")

print(f"wrote {NST} stages of {L} codes (last {N - (NST - 1) * L}) to {OUT}")
