#!/usr/bin/env python3
"""Generate the Lean files for the (6,8) Haar record on 31680 vertices (gaps job, see GAPS.md).

G = PSL(2, 11) x Z24 (order 15840), S = the six elements of research/frontier/sols/d6D8_psl_11_24_orb2f0_s1.txt.
The Haar graph has vertices idx(g) (side A) and 15840 + idx(g) (side B), (g, A) ~ (s g, B).

Group conventions, mirrored exactly by lean/BipartiteDD/Haar/D6D8PSL11Z24/{PSL11,Base}.lean (the PSL(2,11) file is
derived from the PSL(2,19) file of D7D8 by the substitutions of `make_psl11`):
  PSL(2,11): matrices [[a,b],[c,d]] over Z/11 with det 1 modulo ±1; representative with pos(a,c): (a if c == 0 else c) <= 5.
  Product: matrix product, then canon (negate if not pos). Numbering: c == 0 -> (a-1)*11 + b (a in 1..5);
  c != 0 -> 55 + ((c-1)*11 + a)*11 + d (c in 1..5); b = (ad-1)/c.
  G = PSL x Z24, element index n = pIdx*24 + z.

Before writing, the script
  1. reads S from the solution file (header 6 8 psl 11 n 24 N 15840) and canonicalises it,
  2. checks the numbering and the group axioms of the Python mirror,
  3. runs the master builder `research/frontier/build_haar2.py` (imported; its own matrix class gives its element order),
     and checks that the builder's edge list, relabelled into the numbering above, is exactly the Haar graph of S
     (31680 vertices, 95040 edges, 6-regular); the edge list is written into the Lean folder,
  4. finds word codes for each covering pattern of `Eight.lean`: A (8 letters), B (8 letters), C (7 letters),
     each checked in Python against its element. Code digits are base 6 (index of the k-th letter in S).

Covers (Eight.lean): A: x = p1⁻¹ p2 p3⁻¹ p4 p5⁻¹ p6 p7⁻¹ p8; B: x = p1 p2⁻¹ p3 p4⁻¹ p5 p6⁻¹ p7 p8⁻¹;
C: x = p1 p2⁻¹ p3 p4⁻¹ p5 p6⁻¹ p7.  The codes are split into 11 chunks of 1440 (one module each, `chkList`).

usage: python3 research/lean-haarD/gen_d6D8_n31680.py"""
import re
import shutil
import sys
from itertools import product
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
SOL = ROOT / "research/frontier/sols/d6D8_psl_11_24_orb2f0_s1.txt"
FRONTIER = ROOT / "research/frontier"
PSL19_LEAN = ROOT / "lean/BipartiteDD/Haar/D7D8/PSL19.lean"
OUT = ROOT / "lean/BipartiteDD/Haar/D6D8PSL11Z24"
EDGES_NAME = "d6D8_n31680_psl11_z24.edges.txt"
FOLDER = "D6D8PSL11Z24"

P = 11                                     # the prime
HALF = 5                                   # (P - 1) / 2, the representative bound
NZ = 24                                    # the cyclic factor Z24
NP = P * (P * P - 1) // 2                  # |PSL(2,11)| = 660
N = NP * NZ                                # |G| = 15840
K = 6                                      # |S|
CHUNK = 1440
NCH = N // CHUNK
assert N % CHUNK == 0


def inv(x):
    return pow(x, P - 2, P)


def pos(a, c):
    return (a if c == 0 else c) <= HALF


def canon(a, b, c, d):
    a, b, c, d = a % P, b % P, c % P, d % P
    if pos(a, c):
        return (a, b, c, d)
    return ((-a) % P, (-b) % P, (-c) % P, (-d) % P)


def pmul(g, h):
    a, b, c, d = g
    e, f, k, l = h
    return canon(a * e + b * k, a * f + b * l, c * e + d * k, c * f + d * l)


def pinv(g):
    a, b, c, d = g
    return canon(d, -b, -c, a)


ONE = (1, 0, 0, 1)


# the numbering: c == 0 first (55 = 5 * 11 elements), then c != 0 (605 elements); PSL(2,11) has 660 elements
assert 5 * P == 55


def pidx_checked(g):
    a, b, c, d = g
    if c == 0:
        assert 1 <= a <= HALF
        return (a - 1) * P + b
    assert 1 <= c <= HALF
    return 5 * P + ((c - 1) * P + a) * P + d


def quad(n):
    if n < 5 * P:
        a = n // P + 1
        return (a, n % P, 0, inv(a))
    m = n - 5 * P
    c = m // (P * P) + 1
    a = (m // P) % P
    d = m % P
    b = ((a * d - 1) * inv(c)) % P
    return (a, b, c, d)


ELEMS = sorted({canon(a, b, c, d) for a in range(P) for b in range(P) for c in range(P) for d in range(P)
                if (a * d - b * c) % P == 1})
assert len(ELEMS) == NP, len(ELEMS)
assert [pidx_checked(g) for g in ELEMS] and sorted(pidx_checked(g) for g in ELEMS) == list(range(NP))
for n in range(NP):
    g = quad(n)
    assert canon(*g) == g and (g[0] * g[3] - g[1] * g[2]) % P == 1 and pidx_checked(g) == n, n
assert all(pmul(pinv(g), g) == ONE and pmul(g, pinv(g)) == ONE for g in ELEMS[::17])
assert all(pmul(pmul(g, h), k) == pmul(g, pmul(h, k)) for g, h, k in product(ELEMS[::97], ELEMS[::89], ELEMS[::83]))


def enc(elem):                             # index of (g, z) in G: pIdx * 24 + z
    g, z = elem
    return pidx_checked(g) * NZ + z % NZ


def mul(x, y):                             # (g, z)(h, w) = (g h, z + w)
    return (pmul(x[0], y[0]), (x[1] + y[1]) % NZ)


def inv_el(x):
    return (pinv(x[0]), (-x[1]) % NZ)


GROUP = [(g, z) for g in ELEMS for z in range(NZ)]
assert sorted(enc(x) for x in GROUP) == list(range(N))

# 1. the solution file
lines = [ln for ln in SOL.read_text().split("\n") if ln.strip()]
head = lines[0].split()
assert head[:6] == ["6", "8", "psl", "11", "n", "24"] and head[-2:] == ["N", "15840"], head
S = []
for ln in lines[1:1 + K]:
    m = re.fullmatch(r"\s*\d+\s+mat\((\d+),(\d+),(\d+),(\d+)\)\s+z=(\d+)\s*", ln)
    a, b, c, d, z = map(int, m.groups())
    assert (a * d - b * c) % P == 1
    S.append((canon(a, b, c, d), z % NZ))
assert len(S) == K and len(set(S)) == K, S
assert S[0] == (ONE, 0)                    # identity first, as in the solution file

# 2. the master builder, imported, and its edge list relabelled into this numbering
sys.path.insert(0, str(FRONTIER))
import numpy as np  # noqa: E402
import build_haar2 as bh  # noqa: E402

Q = bh.Matrix("psl", P)
assert Q.order == NP
bq = Q.keys                                # the builder's element order: sorted canonical keys
assert len(bq) == NP
n_builder = NZ


def builder_elem(idx):                     # builder index -> (canonical matrix, z) in this numbering
    r, z = divmod(int(idx), n_builder)
    k = int(bq[r])
    a, b, c, d = k // P ** 3, (k // P ** 2) % P, (k // P) % P, k % P
    return (canon(a, b, c, d), z)


import subprocess  # noqa: E402

edges_path = OUT / EDGES_NAME
OUT.mkdir(parents=True, exist_ok=True)
run = subprocess.run([sys.executable, str(FRONTIER / "build_haar2.py"), str(SOL), str(edges_path)],
                     capture_output=True, text=True)
assert run.returncode == 0 and "VALID d=6 D=8" in run.stdout, run.stdout + run.stderr
toks = edges_path.read_text().split()
assert toks[0] == str(2 * N)
file_edges = sorted((int(toks[k]), int(toks[k + 1])) for k in range(1, len(toks), 2))
relabel = {}
for idx in range(N):
    relabel[idx] = enc(builder_elem(idx))
assert sorted(relabel.values()) == list(range(N))
mapped = sorted((relabel[u], N + relabel[v - N]) for u, v in file_edges)
haar_edges = sorted((enc(x), N + enc(mul(s, x))) for x in GROUP for s in S)
assert len(haar_edges) == len(set(haar_edges)) == len(mapped) == K * N
assert mapped == haar_edges, "the builder's edge list, relabelled, differs from the Haar graph of S"

# 3. covering words (as in D7D8): pair sets and their words
SINV = [inv_el(s) for s in S]


def bfs(pairs, depth):
    levels = [{(ONE, 0): ()}]
    for _ in range(depth):
        nxt = {}
        for g, w in levels[-1].items():
            for p, pr in pairs.items():
                x = mul(p, g)
                if x not in nxt:
                    nxt[x] = (pr,) + w
        levels.append(nxt)
    return levels


PA = {}
PB = {}
for i in range(K):
    for j in range(K):
        PA.setdefault(mul(SINV[i], S[j]), (i, j))
        PB.setdefault(mul(S[i], SINV[j]), (i, j))
LA = bfs(PA, 4)
LB = bfs(PB, 4)
assert len(LA[4]) == N and len(LB[4]) == N, ("AA/BB do not cover G", len(LA[4]), len(LB[4]))
L3 = LA[3]

codes = {"A": [0] * N, "B": [0] * N, "C": [0] * N}
POW = [K ** k for k in range(8)]
for n in range(N):
    g = (quad(n // NZ), n % NZ)
    assert enc(g) == n
    # A: (S_d0)^-1 S_d1 (S_d2)^-1 S_d3 ...
    digs = [x for pr in LA[4][g] for x in pr]
    codes["A"][n] = sum(d * POW[k] for k, d in enumerate(digs))
    acc = (ONE, 0)
    for k in range(0, 8, 2):
        acc = mul(acc, mul(SINV[digs[k]], S[digs[k + 1]]))
    assert acc == g, ("A", n)
    # B: S_d0 (S_d1)^-1 S_d2 (S_d3)^-1 ...
    digb = [x for pr in LB[4][g] for x in pr]
    codes["B"][n] = sum(d * POW[k] for k, d in enumerate(digb))
    acc = (ONE, 0)
    for k in range(0, 8, 2):
        acc = mul(acc, mul(S[digb[k]], SINV[digb[k + 1]]))
    assert acc == g, ("B", n)
    # C: S_i * (a1^-1 b1)(a2^-1 b2)(a3^-1 b3), i.e. p1 p2^-1 p3 p4^-1 p5 p6^-1 p7
    found = None
    for i in range(K):
        w = L3.get(mul(SINV[i], g))
        if w is not None:
            found = (i, w)
            break
    assert found is not None, ("C", n)
    i, w = found
    digc = [i] + [x for pr in w for x in pr]
    codes["C"][n] = sum(d * POW[k] for k, d in enumerate(digc))
    acc = S[i]
    for k in range(1, 7, 2):
        acc = mul(acc, mul(SINV[digc[k]], S[digc[k + 1]]))
    assert acc == g, ("C", n)

# ----------------------------------------------------------------------------------------------- Lean text
PSL_TEXT = PSL19_LEAN.read_text()


def make_psl11(t):
    t = t.replace("PSL19", "PSL11").replace("zmod19", "zmod11").replace("inv19", "inv11")
    t = re.sub(r"\bZMod 19\b", "ZMod 11", t)
    t = re.sub(r"\b19\b", "11", t)
    t = t.replace("3420", "660").replace("171", "55").replace("361", "121")
    t = t.replace("≤ 9", "≤ 5").replace("…9", "…5")
    t = re.sub(r"def invTab : List \(ZMod 11\) := \[[^\]]*\]",
               "def invTab : List (ZMod 11) := [0, 1, 6, 4, 3, 9, 2, 8, 7, 5, 10]", t)
    return t


PSL11_LEAN = ("/- Generated by research/lean-haarD/gen_d6D8_n31680.py from lean/BipartiteDD/Haar/D7D8/PSL19.lean "
              "(substitutions only). Do not edit by hand. -/\n" + make_psl11(PSL_TEXT))

BASE = f'''/- Generated by research/lean-haarD/gen_d6D8_n31680.py. Do not edit by hand. -/
import BipartiteDD.Haar.D6D8PSL11Z24.PSL11
import Mathlib.Logic.Equiv.Fin.Basic

/-! The group `G = PSL(2, 11) × Z24` of the Δ6·D8 record (order 15840), and its numbering by `Fin 15840`.
`G` is a structure with its own group instance (the product of the `PSL11` group and `ZMod 24` under addition), as
the `Grp` of the (5,8) record: the product `Multiplicative` type made the covering lemma's unification too slow. -/

namespace BipartiteDD.Haar.D6D8PSL11Z24

open BipartiteDD.Haar.PSL11

/-- The elements `(p, z)` of `PSL(2, 11) × Z24`. -/
@[ext]
structure G where
  p : PSL11.Grp
  z : ZMod 24
  deriving DecidableEq

instance : Group G where
  mul x y := ⟨x.p * y.p, x.z + y.z⟩
  one := ⟨1, 0⟩
  inv x := ⟨x.p⁻¹, -x.z⟩
  mul_assoc x y w := by
    obtain ⟨xp, xz⟩ := x
    obtain ⟨yp, yz⟩ := y
    obtain ⟨wp, wz⟩ := w
    show (⟨xp * yp * wp, xz + yz + wz⟩ : G) = ⟨xp * (yp * wp), xz + (yz + wz)⟩
    rw [mul_assoc, add_assoc]
  one_mul x := by
    obtain ⟨xp, xz⟩ := x
    show (⟨1 * xp, 0 + xz⟩ : G) = ⟨xp, xz⟩
    rw [one_mul, zero_add]
  mul_one x := by
    obtain ⟨xp, xz⟩ := x
    show (⟨xp * 1, xz + 0⟩ : G) = ⟨xp, xz⟩
    rw [mul_one, add_zero]
  inv_mul_cancel x := by
    obtain ⟨xp, xz⟩ := x
    show (⟨xp⁻¹ * xp, -xz + xz⟩ : G) = ⟨1, 0⟩
    rw [inv_mul_cancel, neg_add_cancel]

/-- The index of `(p, z)` is `enc p * 24 + z`. -/
def idxG (g : G) : ℕ := enc g.p.a g.p.b g.p.c g.p.d * 24 + g.z.val

/-- The element with index `n`. -/
def gOf (n : ℕ) : G := ⟨grpP (n / 24), ((n % 24 : ℕ) : ZMod 24)⟩

theorem idxG_lt (g : G) : idxG g < 15840 := by
  have h1 := enc_lt g.p
  have h2 := ZMod.val_lt g.z
  unfold idxG
  omega

theorem gOf_idxG (g : G) : gOf (idxG g) = g := by
  have h2 := ZMod.val_lt g.z
  have h1 : (enc g.p.a g.p.b g.p.c g.p.d * 24 + g.z.val) / 24 = enc g.p.a g.p.b g.p.c g.p.d := by
    omega
  have h3 : (enc g.p.a g.p.b g.p.c g.p.d * 24 + g.z.val) % 24 = g.z.val := by
    omega
  unfold gOf idxG
  rw [h1, h3, grpP_enc, ZMod.natCast_zmod_val]

theorem idxG_gOf (n : ℕ) (hn : n < 15840) : idxG (gOf n) = n := by
  have h1 : enc (grpP (n / 24)).a (grpP (n / 24)).b (grpP (n / 24)).c (grpP (n / 24)).d = n / 24 :=
    enc_grpP (n / 24) (by omega)
  have h2 : ((((n % 24 : ℕ) : ZMod 24)).val) = n % 24 := by
    rw [ZMod.val_natCast, Nat.mod_mod]
  unfold idxG gOf
  dsimp only
  rw [h1, h2]
  omega

/-- The numbering of `G` by `Fin 15840`. -/
def equivG : G ≃ Fin 15840 where
  toFun g := ⟨idxG g, idxG_lt g⟩
  invFun n := gOf n.1
  left_inv g := gOf_idxG g
  right_inv n := Fin.ext (idxG_gOf n.1 n.2)

/-- `G ⊕ G ≃ Fin 31680`: the two sides of the Haar graph. -/
def haarVert : G ⊕ G ≃ Fin 31680 :=
  (Equiv.sumCongr equivG equivG).trans (finSumFinEquiv.trans (finCongr (by norm_num)))

end BipartiteDD.Haar.D6D8PSL11Z24
'''

GENS_HEAD = f'''/- Generated by research/lean-haarD/gen_d6D8_n31680.py. Do not edit by hand. -/
import BipartiteDD.Haar.D6D8PSL11Z24.Base

/-! The six generators `S` of the Δ6·D8 record (`research/frontier/sols/d6D8_psl_11_24_orb2f0_s1.txt`), as elements of
`PSL(2,11) × ZMod 24` in the normal form of `PSL11`; the codes, their digit function and the word functions of the
covering patterns of `Eight.lean`; and the linear check `chkList`. -/

namespace BipartiteDD.Haar.D6D8PSL11Z24

open BipartiteDD.Haar.PSL11

/-- The connection set, as elements `(class, z)` of `PSL(2,11) × Z24`, the identity first. -/
def sS : Fin 6 → G := ![__SLIST__]

/-- `S` as a finset. -/
def SS : Finset G := Finset.univ.image sS

theorem card_SS : SS.card = 6 := by decide +kernel

theorem sS_mem (i : Fin 6) : sS i ∈ SS :=
  Finset.mem_image_of_mem sS (Finset.mem_univ i)

/-- The `k`-th base-6 digit of the code `c`, an index into `sS`. -/
def dig (c k : ℕ) : Fin 6 := ⟨c / 6 ^ k % 6, Nat.mod_lt _ (by norm_num)⟩

/-- Pattern A: `p₁⁻¹ p₂ p₃⁻¹ p₄ p₅⁻¹ p₆ p₇⁻¹ p₈`. -/
def wA (c : ℕ) : G :=
  (sS (dig c 0))⁻¹ * sS (dig c 1) * (sS (dig c 2))⁻¹ * sS (dig c 3) * (sS (dig c 4))⁻¹ * sS (dig c 5) *
    (sS (dig c 6))⁻¹ * sS (dig c 7)

/-- Pattern B: `p₁ p₂⁻¹ p₃ p₄⁻¹ p₅ p₆⁻¹ p₇ p₈⁻¹`. -/
def wB (c : ℕ) : G :=
  sS (dig c 0) * (sS (dig c 1))⁻¹ * sS (dig c 2) * (sS (dig c 3))⁻¹ * sS (dig c 4) * (sS (dig c 5))⁻¹ *
    sS (dig c 6) * (sS (dig c 7))⁻¹

/-- Pattern C: `p₁ p₂⁻¹ p₃ p₄⁻¹ p₅ p₆⁻¹ p₇` (seven letters). -/
def wC (c : ℕ) : G :=
  sS (dig c 0) * (sS (dig c 1))⁻¹ * sS (dig c 2) * (sS (dig c 3))⁻¹ * sS (dig c 4) * (sS (dig c 5))⁻¹ *
    sS (dig c 6)

/-- The codes `l` from index `n` on: the word of code `c` at index `n` is `gOf n`. -/
def chkList (w : ℕ → G) : ℕ → List ℕ → Bool
  | _, [] => true
  | n, c :: cs => decide (gOf n = w c) && chkList w (n + 1) cs

theorem chkList_spec (w : ℕ → G) : ∀ (l : List ℕ) (n : ℕ), chkList w n l = true →
    ∀ j < l.length, gOf (n + j) = w (l.getD j 0)
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | c :: cs, n, h, j, hj => by
    simp only [chkList, Bool.and_eq_true, decide_eq_true_eq] at h
    cases j with
    | zero => simpa using h.1
    | succ j =>
      have h2 := chkList_spec w cs (n + 1) h.2 j (by simpa using hj)
      have e : n + (j + 1) = n + 1 + j := by omega
      rw [e]
      simpa using h2

/-- A checked chunk gives the words of its indices. -/
theorem exists_word (w : ℕ → G) (l : List ℕ) (lo L n : ℕ) (hl : chkList w lo l = true)
    (hlen : l.length = L) (h1 : lo ≤ n) (h2 : n < lo + L) : ∃ c, gOf n = w c := by
  have h := chkList_spec w l lo hl (n - lo) (by rw [hlen]; omega)
  have e : lo + (n - lo) = n := by omega
  rw [e] at h
  exact ⟨_, h⟩

end BipartiteDD.Haar.D6D8PSL11Z24
'''


def chunk_module(pattern, k, codelist):
    lo, hi = k * CHUNK, (k + 1) * CHUNK
    items = [str(c) for c in codelist[lo:hi]]
    rows = [", ".join(items[t:t + 16]) for t in range(0, len(items), 16)]
    body = ",\n    ".join(rows)
    return f'''/- Generated by research/lean-haarD/gen_d6D8_n31680.py. Do not edit by hand. -/
import BipartiteDD.Haar.D6D8PSL11Z24.Gens

/-! Pattern {pattern}, chunk {k}: the codes of the group elements `n ∈ [{lo}, {hi})`, checked by `decide +kernel`. -/

namespace BipartiteDD.Haar.D6D8PSL11Z24

set_option maxRecDepth 100000 in
/-- The codes of pattern {pattern} from index {lo}. -/
def cert{pattern}{k} : List ℕ :=
    [{body}]

set_option maxRecDepth 100000 in
theorem len{pattern}{k} : cert{pattern}{k}.length = {CHUNK} := by rfl

set_option maxRecDepth 100000 in
theorem ok{pattern}{k} : chkList w{pattern} {lo} cert{pattern}{k} = true := by decide +kernel

end BipartiteDD.Haar.D6D8PSL11Z24
'''


def cover_file():
    lines = [
        "/- Generated by research/lean-haarD/gen_d6D8_n31680.py. Do not edit by hand. -/",
        "import BipartiteDD.Haar.D6D8PSL11Z24.Gens",
    ]
    for p in "ABC":
        for k in range(NCH):
            lines.append(f"import BipartiteDD.Haar.D6D8PSL11Z24.Cert{p}{k}")
    lines += ["", "/-! The covering hypotheses of `Eight.lean` for the (6,8) Haar record on 31680 vertices, from the chunks of",
              "`CertA0 … CertC10`, each checked by `decide +kernel`. -/", "",
              "namespace BipartiteDD.Haar.D6D8PSL11Z24", "", "open BipartiteDD.Haar.PSL11", ""]
    for p in "ABC":
        lines.append(f"theorem all{p} (n : ℕ) (hn : n < {N}) : ∃ c, gOf n = w{p} c := by")
        for k in range(NCH - 1):
            lo, hi = k * CHUNK, (k + 1) * CHUNK
            lines.append(f"  by_cases h{k} : n < {hi}")
            lines.append(f"  · exact exists_word w{p} cert{p}{k} {lo} {CHUNK} n ok{p}{k} len{p}{k} (by omega) (by omega)")
        k = NCH - 1
        lo = k * CHUNK
        lines.append(f"  exact exists_word w{p} cert{p}{k} {lo} {CHUNK} n ok{p}{k} len{p}{k} (by omega) (by omega)")
        lines.append("")
    lines += [
        "theorem coverA : ∀ g : G, ∃ p₁ ∈ SS, ∃ p₂ ∈ SS, ∃ p₃ ∈ SS, ∃ p₄ ∈ SS, ∃ p₅ ∈ SS, ∃ p₆ ∈ SS,",
        "    ∃ p₇ ∈ SS, ∃ p₈ ∈ SS, g = p₁⁻¹ * p₂ * p₃⁻¹ * p₄ * p₅⁻¹ * p₆ * p₇⁻¹ * p₈ := by",
        "  intro g",
        "  obtain ⟨c, hc⟩ := allA (idxG g) (idxG_lt g)",
        "  rw [gOf_idxG] at hc",
        "  unfold wA at hc",
        "  exact ⟨sS (dig c 0), sS_mem _, sS (dig c 1), sS_mem _, sS (dig c 2), sS_mem _, sS (dig c 3), sS_mem _,",
        "    sS (dig c 4), sS_mem _, sS (dig c 5), sS_mem _, sS (dig c 6), sS_mem _, sS (dig c 7), sS_mem _, hc⟩",
        "",
        "theorem coverB : ∀ g : G, ∃ p₁ ∈ SS, ∃ p₂ ∈ SS, ∃ p₃ ∈ SS, ∃ p₄ ∈ SS, ∃ p₅ ∈ SS, ∃ p₆ ∈ SS,",
        "    ∃ p₇ ∈ SS, ∃ p₈ ∈ SS, g = p₁ * p₂⁻¹ * p₃ * p₄⁻¹ * p₅ * p₆⁻¹ * p₇ * p₈⁻¹ := by",
        "  intro g",
        "  obtain ⟨c, hc⟩ := allB (idxG g) (idxG_lt g)",
        "  rw [gOf_idxG] at hc",
        "  unfold wB at hc",
        "  exact ⟨sS (dig c 0), sS_mem _, sS (dig c 1), sS_mem _, sS (dig c 2), sS_mem _, sS (dig c 3), sS_mem _,",
        "    sS (dig c 4), sS_mem _, sS (dig c 5), sS_mem _, sS (dig c 6), sS_mem _, sS (dig c 7), sS_mem _, hc⟩",
        "",
        "theorem coverC : ∀ g : G, ∃ p₁ ∈ SS, ∃ p₂ ∈ SS, ∃ p₃ ∈ SS, ∃ p₄ ∈ SS, ∃ p₅ ∈ SS, ∃ p₆ ∈ SS,",
        "    ∃ p₇ ∈ SS, g = p₁ * p₂⁻¹ * p₃ * p₄⁻¹ * p₅ * p₆⁻¹ * p₇ := by",
        "  intro g",
        "  obtain ⟨c, hc⟩ := allC (idxG g) (idxG_lt g)",
        "  rw [gOf_idxG] at hc",
        "  unfold wC at hc",
        "  exact ⟨sS (dig c 0), sS_mem _, sS (dig c 1), sS_mem _, sS (dig c 2), sS_mem _, sS (dig c 3), sS_mem _,",
        "    sS (dig c 4), sS_mem _, sS (dig c 5), sS_mem _, sS (dig c 6), sS_mem _, hc⟩",
        "",
        "end BipartiteDD.Haar.D6D8PSL11Z24",
        "",
    ]
    return "\n".join(lines)


RECORD = '''import BipartiteDD.Haar.Eight
import BipartiteDD.Haar.D6D8PSL11Z24.Cover

/-! The (6,8) record on 31680 vertices, as the Haar graph of `G = PSL(2,11) × Z24` (order 15840) with the connection set
`S` of `research/frontier/sols/d6D8_psl_11_24_orb2f0_s1.txt`. The covering hypotheses of the diameter-8 lemma `Eight.lean`
are the kernel-checked chunks of `D6D8PSL11Z24.Cover`. -/

open BipartiteDD.Haar.D6D8PSL11Z24 in
/-- A graph on 31680 vertices, bipartite, of degree at most 6 and diameter at most 8. -/
theorem nb_6_8_n31680 : ∃ G : SimpleGraph (Fin 31680), BipartiteDD.IsBipartiteDegDiam G 6 8 := by
  have h := BipartiteDD.Haar.isBipartiteDegDiam_eight_of SS
    ((BipartiteDD.Haar.haarGraph SS).comap haarVert.symm) haarVert
    (fun x y => by simp [SimpleGraph.comap_adj]) coverA coverB coverC
  rw [card_SS] at h
  exact ⟨_, h⟩
'''

AXIOMS = "import BipartiteDD.Haar.D6D8PSL11Z24.Record31680\n\n#print axioms nb_6_8_n31680\n"


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "PSL11.lean").write_text(PSL11_LEAN)
    (OUT / "Base.lean").write_text(BASE)
    slist = ",\n    ".join(f"⟨⟨{g[0]}, {g[1]}, {g[2]}, {g[3]}, by decide, by decide⟩, {z}⟩" for g, z in S)
    (OUT / "Gens.lean").write_text(GENS_HEAD.replace("__SLIST__", "\n    " + slist))
    for p in "ABC":
        for k in range(NCH):
            (OUT / f"Cert{p}{k}.lean").write_text(chunk_module(p, k, codes[p]))
    (OUT / "Cover.lean").write_text(cover_file())
    (OUT / "Record31680.lean").write_text(RECORD)
    (OUT / "Axioms.lean").write_text(AXIOMS)
    shutil.copyfile(SOL, OUT / SOL.name)
    print("ok: wrote", OUT, "| S =", S, "| builder edge list, relabelled, equals the Haar graph of S:", len(mapped),
          "edges | codes checked:", {p: len(codes[p]) for p in codes})


if __name__ == "__main__":
    main()
