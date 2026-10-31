#!/usr/bin/env python3
"""Generate the Lean files for the (5,8) Haar record on 9760 vertices (gaps job, see GAPS.md).

G = Z61 x|_8 Z80 (the metacyclic group `meta 61 80 8` of research/frontier/build_haar2.py): elements x^i y^j written
(i, j) with (i, j)(a, b) = (i + 8^j a, j + b). S = the five elements of research/frontier/sols/d5D8_n9760_haar_meta61_80_8_s1.txt.
The Haar graph has vertices enc(g) (side A) and 4880 + enc(g) (side B), with (g, A) ~ (s g, B); enc(i, j) = 80 i + j.

Before writing, the script
  1. reads S from the solution file and checks its header (meta 61 80 8, N 4880, n 1, d 5, D 8),
  2. runs research/frontier/build_haar2.py on it (the master builder: all-pairs BFS check, prints VALID), writes its
     edge list into the Lean folder, and checks that this edge list equals the Haar graph of S under the numbering above
     (9760 vertices, 24400 edges, 5-regular),
  3. finds for every element g a word code for each covering pattern of `Eight.lean`: A (eight letters),
     B (eight letters) and C (seven letters). A code is base 5, digit k is the index of the k-th letter in S.
     Entry n of the code list of a pattern is a code of a word for `grpOf n`.

The codes are split into chunks of 1220 entries (one Lean module per chunk, each checked by `decide +kernel` with the
linear list check `chkList`, as in D7D8); `Cover.lean` gives the covering hypotheses of `Eight.lean`.

Writes lean/BipartiteDD/Haar/D5D8N9760/{Grp,Gens,CertA0..3,CertB0..3,CertC0..3,Cover,Record9760,Axioms}.lean and the
edge list and the solution file.
usage: python3 research/lean-haarD/gen_d5D8_n9760.py"""
import shutil
import subprocess
import sys
from itertools import product
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
SOL = ROOT / "research/frontier/sols/d5D8_n9760_haar_meta61_80_8_s1.txt"
BUILDER = ROOT / "research/frontier/build_haar2.py"
OUT = ROOT / "lean/BipartiteDD/Haar/D5D8N9760"
EDGES_NAME = "d5D8_n9760_haar_meta61_80_8.edges.txt"

M, K, R = 61, 80, 8                        # x has order 61, y has order 80, y x y^-1 = x^R
N = M * K                                  # |G| = 4880
DEG_D = 5                                  # valency |S|
CHUNK = 1220                               # codes per Lean module
assert N % CHUNK == 0
NCH = N // CHUNK

lines = SOL.read_text().splitlines()
hdr = lines[0].split()
assert hdr[:2] == ["5", "8"] and hdr[2:5] == ["meta", "61", "80"] and hdr[5] == "8" and hdr[-2:] == ["N", "4880"], hdr
S = []
for line in lines[1:]:
    if not line.strip():
        continue
    idx, rest = line.split(None, 1)
    a, j = (int(t.split("=")[1]) for t in rest.split("(")[1].split(")")[0].split(","))
    assert int(idx) == a * K + j, (idx, a, j)
    S.append((a, j))
assert len(S) == DEG_D and len(set(S)) == DEG_D

RP = [pow(R, j, M) for j in range(K)]
assert pow(R, K, M) == 1


def mul(g, h):                             # (i, j)(a, b) = (i + r^j a, j + b)
    return ((g[0] + RP[g[1]] * h[0]) % M, (g[1] + h[1]) % K)


def inv(g):                                # (i, j)^-1 = (-r^(-j) i, -j)
    return ((-(RP[(-g[1]) % K] * g[0])) % M, (-g[1]) % K)


def enc(g):
    return g[0] * K + g[1]


def grp_of(n):
    return (n // K, n % K)


ELEMS = [(i, j) for i in range(M) for j in range(K)]
assert sorted(enc(g) for g in ELEMS) == list(range(N))
assert all(mul(g, inv(g)) == (0, 0) and mul(inv(g), g) == (0, 0) for g in ELEMS)

# 2. the master builder, then the comparison with the Haar graph of S
OUT.mkdir(parents=True, exist_ok=True)
edges_path = OUT / EDGES_NAME
res = subprocess.run([sys.executable, str(BUILDER), str(SOL), str(edges_path)], capture_output=True, text=True)
assert res.returncode == 0 and "VALID d=5 D=8" in res.stdout, res.stdout + res.stderr
toks = edges_path.read_text().split()
assert toks[0] == str(2 * N)
file_edges = sorted((int(toks[k]), int(toks[k + 1])) for k in range(1, len(toks), 2))
haar_edges = sorted((enc(g), N + enc(mul(s, g))) for g in ELEMS for s in S)
assert len(haar_edges) == len(set(haar_edges)) == len(file_edges) == DEG_D * N
assert file_edges == haar_edges, "Haar graph of S differs from the builder's edge list"

# 3. covering codes. Word of pattern X with code c: letter k is S[digit k of c].
PATTERNS = {
    "A": (8, lambda p: mul(mul(mul(mul(mul(mul(mul(inv(p[0]), p[1]), inv(p[2])), p[3]), inv(p[4])), p[5]), inv(p[6])), p[7])),
    "B": (8, lambda p: mul(mul(mul(mul(mul(mul(mul(p[0], inv(p[1])), p[2]), inv(p[3])), p[4]), inv(p[5])), p[6]), inv(p[7]))),
    "C": (7, lambda p: mul(mul(mul(mul(mul(mul(p[0], inv(p[1])), p[2]), inv(p[3])), p[4]), inv(p[5])), p[6])),
}


def digits_of(c, length):
    return [(c // DEG_D ** k) % DEG_D for k in range(length)]


def find(length, word):
    tab = {}
    for c in range(DEG_D ** length):
        g = word([S[d] for d in digits_of(c, length)])
        tab.setdefault(enc(g), c)
    assert len(tab) == N, f"pattern covers only {len(tab)} of {N} elements"
    return [tab[n] for n in range(N)]


codes = {name: find(length, word) for name, (length, word) in PATTERNS.items()}
for name, (length, word) in PATTERNS.items():          # every code is checked against its element
    for n in range(N):
        assert word([S[d] for d in digits_of(codes[name][n], length)]) == grp_of(n), (name, n)

# ----------------------------------------------------------------------------------------------- Lean text
GRP = '''/- Generated by research/lean-haarD/gen_d5D8_n9760.py. Do not edit by hand. -/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Logic.Equiv.Fin.Basic

/-! The metacyclic group `G = C61 : C80 = ⟨x, y | x^61 = y^80 = 1, y x y⁻¹ = x^8⟩` (y acts with order 80), the group
of the (5,8) Haar record on 9760 vertices. An element `x^i y^j` is the pair `(i, j) ∈ ZMod 61 × ZMod 80`; the product
is `(i, j) (a, b) = (i + r^j a, j + b)` with `r = 8`, since `y^j x y^-j = x^(r^j)`. The numbering `G ≃ Fin 4880` is
`(i, j) ↦ 80 i + j`, the numbering of the Haar graph in `research/frontier/build_haar2.py`. -/

namespace BipartiteDD.Haar.D5D8N9760

/-- The elements `x^i y^j` of `G`. A structure, so that no other multiplication on the pairs is in scope. -/
@[ext] structure Grp where
  i : ZMod 61
  j : ZMod 80
  deriving DecidableEq

/-- `r^j` for `r = 8`, the action of `y^j` on `x`. It depends on `j` only through `j mod 80`, since `8^80 = 1` in
`ZMod 61` (the order of `8` mod `61` divides `80`). It is the natural number `8 ^ j.val` cast to `ZMod 61`, so that the
kernel evaluates the power with its accelerated `Nat.pow`. -/
def rpow (j : ZMod 80) : ZMod 61 := ((8 ^ j.val : ℕ) : ZMod 61)

theorem rpow_add (j b : ZMod 80) : rpow (j + b) = rpow j * rpow b := by
  unfold rpow
  revert j b
  decide +kernel

instance : Group Grp where
  mul g h := ⟨g.i + rpow g.j * h.i, g.j + h.j⟩
  one := ⟨0, 0⟩
  inv g := ⟨-(rpow (-g.j) * g.i), -g.j⟩
  mul_assoc g h k := by
    show (⟨g.i + rpow g.j * h.i + rpow (g.j + h.j) * k.i, g.j + h.j + k.j⟩ : Grp) =
      ⟨g.i + rpow g.j * (h.i + rpow h.j * k.i), g.j + (h.j + k.j)⟩
    rw [rpow_add]
    congr 1 <;> ring
  one_mul g := by
    obtain ⟨gi, gj⟩ := g
    have h0 : rpow 0 = 1 := by simp [rpow]
    show (⟨0 + rpow 0 * gi, 0 + gj⟩ : Grp) = ⟨gi, gj⟩
    simp [h0]
  mul_one g := by
    obtain ⟨gi, gj⟩ := g
    show (⟨gi + rpow gj * 0, gj + 0⟩ : Grp) = ⟨gi, gj⟩
    simp
  inv_mul_cancel g := by
    obtain ⟨gi, gj⟩ := g
    show (⟨-(rpow (-gj) * gi) + rpow (-gj) * gi, -gj + gj⟩ : Grp) = ⟨0, 0⟩
    simp

/-- The numbering of `G` by `0 … 4879`: `x^i y^j ↦ 80 i + j`. -/
def enc (g : Grp) : ℕ := g.i.val * 80 + g.j.val

theorem enc_lt (g : Grp) : enc g < 4880 := by
  have h1 := ZMod.val_lt g.i
  have h2 := ZMod.val_lt g.j
  unfold enc
  omega

/-- The inverse of `enc` on `0 … 4879`. -/
def grpOf (n : ℕ) : Grp := ⟨((n / 80 : ℕ) : ZMod 61), ((n % 80 : ℕ) : ZMod 80)⟩

theorem grpOf_enc (g : Grp) : grpOf (enc g) = g := by
  have h2 := ZMod.val_lt g.j
  have hd : (g.i.val * 80 + g.j.val) / 80 = g.i.val := by omega
  have hm : (g.i.val * 80 + g.j.val) % 80 = g.j.val := by omega
  unfold grpOf enc
  rw [hd, hm, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

/-- The numbering of `G`: `Grp ≃ Fin 4880`. -/
def equiv4880 : Grp ≃ Fin 4880 where
  toFun g := ⟨enc g, enc_lt g⟩
  invFun n := grpOf n.1
  left_inv g := grpOf_enc g
  right_inv n := by
    apply Fin.ext
    have hn := n.2
    show enc (grpOf n.1) = n.1
    unfold enc grpOf
    simp only [ZMod.val_natCast]
    omega

end BipartiteDD.Haar.D5D8N9760
'''

GENS = '''/- Generated by research/lean-haarD/gen_d5D8_n9760.py. Do not edit by hand. -/
import BipartiteDD.Haar.D5D8N9760.Grp

/-! The connection set `S` of the (5,8) Haar record on 9760 vertices: the five elements of
`research/frontier/sols/d5D8_n9760_haar_meta61_80_8_s1.txt` as `x^i y^j`, the base-5 digit function of the codes, the
three word functions `wA`, `wB`, `wC` of the covering patterns of `Eight.lean`, and the linear check `chkList`. -/

namespace BipartiteDD.Haar.D5D8N9760

/-- The connection set `S = {__S_TEXT__}`, as `x^i y^j`. -/
def sS : Fin 5 → Grp := ![__S_LEAN__]

/-- `S` as a finset. -/
def SS : Finset Grp := Finset.univ.image sS

theorem card_SS : SS.card = 5 := by decide +kernel

theorem sS_mem (i : Fin 5) : sS i ∈ SS :=
  Finset.mem_image_of_mem sS (Finset.mem_univ i)

/-- The `k`-th base-5 digit of the code `c`, an index into `sS`. -/
def dig (c k : ℕ) : Fin 5 := ⟨c / 5 ^ k % 5, Nat.mod_lt _ (by norm_num)⟩

/-- Pattern A: `p₁⁻¹ p₂ p₃⁻¹ p₄ p₅⁻¹ p₆ p₇⁻¹ p₈`, with the letters given by the digits of `c`. -/
def wA (c : ℕ) : Grp :=
  (sS (dig c 0))⁻¹ * sS (dig c 1) * (sS (dig c 2))⁻¹ * sS (dig c 3) * (sS (dig c 4))⁻¹ * sS (dig c 5) *
    (sS (dig c 6))⁻¹ * sS (dig c 7)

/-- Pattern B: `p₁ p₂⁻¹ p₃ p₄⁻¹ p₅ p₆⁻¹ p₇ p₈⁻¹`. -/
def wB (c : ℕ) : Grp :=
  sS (dig c 0) * (sS (dig c 1))⁻¹ * sS (dig c 2) * (sS (dig c 3))⁻¹ * sS (dig c 4) * (sS (dig c 5))⁻¹ *
    sS (dig c 6) * (sS (dig c 7))⁻¹

/-- Pattern C: `p₁ p₂⁻¹ p₃ p₄⁻¹ p₅ p₆⁻¹ p₇` (seven letters). -/
def wC (c : ℕ) : Grp :=
  sS (dig c 0) * (sS (dig c 1))⁻¹ * sS (dig c 2) * (sS (dig c 3))⁻¹ * sS (dig c 4) * (sS (dig c 5))⁻¹ *
    sS (dig c 6)

/-- The codes `l` from index `n` on: the word of code `c` at index `n` is `grpOf n`. -/
def chkList (w : ℕ → Grp) : ℕ → List ℕ → Bool
  | _, [] => true
  | n, c :: cs => decide (grpOf n = w c) && chkList w (n + 1) cs

theorem chkList_spec (w : ℕ → Grp) : ∀ (l : List ℕ) (n : ℕ), chkList w n l = true →
    ∀ j < l.length, grpOf (n + j) = w (l.getD j 0)
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
theorem exists_word (w : ℕ → Grp) (l : List ℕ) (lo L n : ℕ) (hl : chkList w lo l = true)
    (hlen : l.length = L) (h1 : lo ≤ n) (h2 : n < lo + L) : ∃ c, grpOf n = w c := by
  have h := chkList_spec w l lo hl (n - lo) (by rw [hlen]; omega)
  have e : lo + (n - lo) = n := by omega
  rw [e] at h
  exact ⟨_, h⟩

end BipartiteDD.Haar.D5D8N9760
'''


def chunk_module(pattern, k, codelist):
    lo = k * CHUNK
    items = [str(c) for c in codelist[lo:lo + CHUNK]]
    rows = [", ".join(items[t:t + 16]) for t in range(0, len(items), 16)]
    body = ",\n    ".join(rows)
    return f'''/- Generated by research/lean-haarD/gen_d5D8_n9760.py. Do not edit by hand. -/
import BipartiteDD.Haar.D5D8N9760.Gens

/-! Pattern {pattern}, chunk {k}: the codes of the group elements `n ∈ [{lo}, {lo + CHUNK})`, checked by `decide +kernel`. -/

namespace BipartiteDD.Haar.D5D8N9760

set_option maxRecDepth 100000 in
/-- The codes of pattern {pattern} from index {lo}. -/
def cert{pattern}{k} : List ℕ :=
    [{body}]

set_option maxRecDepth 100000 in
theorem len{pattern}{k} : cert{pattern}{k}.length = {CHUNK} := by rfl

set_option maxRecDepth 100000 in
theorem ok{pattern}{k} : chkList w{pattern} {lo} cert{pattern}{k} = true := by decide +kernel

end BipartiteDD.Haar.D5D8N9760
'''


def cover_file():
    lines = [
        "/- Generated by research/lean-haarD/gen_d5D8_n9760.py. Do not edit by hand. -/",
        "import BipartiteDD.Haar.D5D8N9760.Gens",
    ]
    for p in "ABC":
        for k in range(NCH):
            lines.append(f"import BipartiteDD.Haar.D5D8N9760.Cert{p}{k}")
    lines += ["", "/-! The covering hypotheses of `Eight.lean` for the (5,8) Haar record on 9760 vertices, from the chunks of",
              "`CertA0 … CertC3`, each checked by `decide +kernel`. -/", "",
              "namespace BipartiteDD.Haar.D5D8N9760", ""]
    for p in "ABC":
        lo_hyps = []
        ranges = []
        for k in range(NCH):
            lo = k * CHUNK
            ranges.append(f"  by_cases h{k} : n < {lo + CHUNK}\n"
                          f"  · exact exists_word w{p} cert{p}{k} {lo} {CHUNK} n ok{p}{k} len{p}{k} (by omega) (by omega)")
        body = "\n".join(ranges[:-1]) + f"\n  exact exists_word w{p} cert{p}{NCH - 1} {(NCH - 1) * CHUNK} {CHUNK} n " \
            f"ok{p}{NCH - 1} len{p}{NCH - 1} (by omega) (by omega)"
        # the by_cases ladder: each branch needs the previous guards to be false, which omega reads from the context
        lines.append(f"theorem all{p} (n : ℕ) (hn : n < {N}) : ∃ c, grpOf n = w{p} c := by")
        lines.append(body.replace("  · exact", "  · exact"))
        lines.append("")
    # covering hypotheses in the form of Eight.lean
    lines += [
        "theorem coverA : ∀ g : Grp, ∃ p₁ ∈ SS, ∃ p₂ ∈ SS, ∃ p₃ ∈ SS, ∃ p₄ ∈ SS, ∃ p₅ ∈ SS, ∃ p₆ ∈ SS,",
        "    ∃ p₇ ∈ SS, ∃ p₈ ∈ SS, g = p₁⁻¹ * p₂ * p₃⁻¹ * p₄ * p₅⁻¹ * p₆ * p₇⁻¹ * p₈ := by",
        "  intro g",
        f"  obtain ⟨c, hc⟩ := allA (enc g) (enc_lt g)",
        "  rw [grpOf_enc] at hc",
        "  unfold wA at hc",
        "  exact ⟨sS (dig c 0), sS_mem _, sS (dig c 1), sS_mem _, sS (dig c 2), sS_mem _, sS (dig c 3), sS_mem _,",
        "    sS (dig c 4), sS_mem _, sS (dig c 5), sS_mem _, sS (dig c 6), sS_mem _, sS (dig c 7), sS_mem _, hc⟩",
        "",
        "theorem coverB : ∀ g : Grp, ∃ p₁ ∈ SS, ∃ p₂ ∈ SS, ∃ p₃ ∈ SS, ∃ p₄ ∈ SS, ∃ p₅ ∈ SS, ∃ p₆ ∈ SS,",
        "    ∃ p₇ ∈ SS, ∃ p₈ ∈ SS, g = p₁ * p₂⁻¹ * p₃ * p₄⁻¹ * p₅ * p₆⁻¹ * p₇ * p₈⁻¹ := by",
        "  intro g",
        "  obtain ⟨c, hc⟩ := allB (enc g) (enc_lt g)",
        "  rw [grpOf_enc] at hc",
        "  unfold wB at hc",
        "  exact ⟨sS (dig c 0), sS_mem _, sS (dig c 1), sS_mem _, sS (dig c 2), sS_mem _, sS (dig c 3), sS_mem _,",
        "    sS (dig c 4), sS_mem _, sS (dig c 5), sS_mem _, sS (dig c 6), sS_mem _, sS (dig c 7), sS_mem _, hc⟩",
        "",
        "theorem coverC : ∀ g : Grp, ∃ p₁ ∈ SS, ∃ p₂ ∈ SS, ∃ p₃ ∈ SS, ∃ p₄ ∈ SS, ∃ p₅ ∈ SS, ∃ p₆ ∈ SS,",
        "    ∃ p₇ ∈ SS, g = p₁ * p₂⁻¹ * p₃ * p₄⁻¹ * p₅ * p₆⁻¹ * p₇ := by",
        "  intro g",
        "  obtain ⟨c, hc⟩ := allC (enc g) (enc_lt g)",
        "  rw [grpOf_enc] at hc",
        "  unfold wC at hc",
        "  exact ⟨sS (dig c 0), sS_mem _, sS (dig c 1), sS_mem _, sS (dig c 2), sS_mem _, sS (dig c 3), sS_mem _,",
        "    sS (dig c 4), sS_mem _, sS (dig c 5), sS_mem _, sS (dig c 6), sS_mem _, hc⟩",
        "",
        "end BipartiteDD.Haar.D5D8N9760",
        "",
    ]
    return "\n".join(lines)


RECORD = '''import BipartiteDD.Haar.Eight
import BipartiteDD.Haar.D5D8N9760.Cover

/-! The (5,8) record on 9760 vertices, as the Haar graph of `G = C61 : C80` (y acts with order 80) with the connection set
`S` of `research/frontier/sols/d5D8_n9760_haar_meta61_80_8_s1.txt`. The covering hypotheses of the Haar lemma of
`Eight.lean` are the kernel-checked chunks of `D5D8N9760.Cover`. -/

namespace BipartiteDD.Haar.D5D8N9760

/-- `Grp ⊕ Grp ≃ Fin 9760`: the two sides of the Haar graph, numbered `0 … 9759`. -/
def equiv9760 : Grp ⊕ Grp ≃ Fin 9760 :=
  (Equiv.sumCongr equiv4880 equiv4880).trans (finSumFinEquiv.trans (finCongr (by norm_num)))

end BipartiteDD.Haar.D5D8N9760

open BipartiteDD.Haar.D5D8N9760 in
/-- A graph on 9760 vertices, bipartite, of degree at most 5 and diameter at most 8. -/
theorem nb_5_8_n9760 : ∃ G : SimpleGraph (Fin 9760), BipartiteDD.IsBipartiteDegDiam G 5 8 := by
  have h := BipartiteDD.Haar.isBipartiteDegDiam_eight_of SS
    ((BipartiteDD.Haar.haarGraph SS).comap equiv9760.symm) equiv9760
    (fun x y => by simp [SimpleGraph.comap_adj]) coverA coverB coverC
  rw [card_SS] at h
  exact ⟨_, h⟩
'''

AXIOMS = "import BipartiteDD.Haar.D5D8N9760.Record9760\n\n#print axioms nb_5_8_n9760\n"


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "Grp.lean").write_text(GRP)
    s_text = ", ".join("(%d,%d)" % s for s in S)
    s_lean = ", ".join("⟨%d, %d⟩" % s for s in S)
    (OUT / "Gens.lean").write_text(GENS.replace("__S_TEXT__", s_text).replace("__S_LEAN__", s_lean))
    for p in "ABC":
        for k in range(NCH):
            (OUT / f"Cert{p}{k}.lean").write_text(chunk_module(p, k, codes[p]))
    (OUT / "Cover.lean").write_text(cover_file())
    (OUT / "Record9760.lean").write_text(RECORD)
    (OUT / "Axioms.lean").write_text(AXIOMS)
    shutil.copyfile(SOL, OUT / SOL.name)
    print("ok: wrote", OUT, "| S =", S, "| Haar graph of S equals the builder's edge list:", len(haar_edges), "edges",
          "| codes checked:", {p: len(codes[p]) for p in codes})


if __name__ == "__main__":
    main()
