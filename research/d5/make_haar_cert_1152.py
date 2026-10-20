"""Lean certificates for the (7,5) Haar record on 1152 vertices: the Haar graph of S_4 x Z_24.

  python3 research/d5/make_haar_cert_1152.py          (from the repository root)

Writes lean/BipartiteDD/Haar/Cert1152.lean. The group and the numbering of its elements are in
lean/BipartiteDD/Haar/S4Z24.lean (hand-written); this script follows the same conventions:

  Group G = Equiv.Perm (Fin 4) x Multiplicative (ZMod 24), order 576, product (f, c)(h, d) = (f o h, c + d).
  A permutation is a tuple f with f[i] = f(i), so (f o h)[i] = f[h[i]].
  Index n < 576 is the element (perm number n % 24 in lexicographic order of one-line forms, n // 24).

The connection set S is the seven elements of docs/lean-1152-brief.md. For every n, a certificate lists
indices (i, j, k, l) into S with

  cert1: g = s_i^-1 * s_j * s_k^-1 * s_l        (covers (S^-1 S)^2)
  cert2: g = s_i * s_j^-1 * s_k * s_l^-1        (covers (S S^-1)^2)

where g is the element with index n. Before writing, the script re-checks every certificate and runs a
breadth-first search on the Haar graph (vertices (g, A), (g, B), edges (g, A) ~ (s g, B)): 7-regular,
bipartite, 1152 vertices, diameter 5. Lean re-checks every entry with `decide +kernel`; the certificates
are not trusted. (Adapted from the first version of this script by the Haiku session on
claude/lean-1152-4u9f42.)
"""
import itertools
import sys
from collections import deque
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LEAN = ROOT / "lean" / "BipartiteDD" / "Haar"

M = 24
PERMS = list(itertools.permutations(range(4)))  # lexicographic: the order of `permTab` in S4Z24.lean
PERM_INDEX = {p: i for i, p in enumerate(PERMS)}
N = 576

# Connection set S: (permutation in one-line form [f 0, f 1, f 2, f 3], element of Z_24).
S = [
    ((0, 1, 2, 3), 0),
    ((1, 0, 3, 2), 23),
    ((3, 1, 0, 2), 0),
    ((2, 1, 0, 3), 18),
    ((1, 2, 3, 0), 18),
    ((0, 2, 3, 1), 17),
    ((0, 2, 1, 3), 3),
]


def mul(g, h):
    (f, c), (k, d) = g, h
    return (tuple(f[k[i]] for i in range(4)), (c + d) % M)


def inv(g):
    f, c = g
    finv = [0] * 4
    for i in range(4):
        finv[f[i]] = i
    return (tuple(finv), (-c) % M)


def elem(n):
    """The element with index n < 576."""
    return (PERMS[n % 24], n // 24)


ALL = [elem(n) for n in range(N)]
assert len(set(ALL)) == N
assert len(set(S)) == 7


def form1(s, t):
    """s^-1 t, the factor of cert1 (g = (s_i^-1 s_j)(s_k^-1 s_l))."""
    return mul(inv(s), t)


def form2(s, t):
    """s t^-1, the factor of cert2 (g = (s_i s_j^-1)(s_k s_l^-1))."""
    return mul(s, inv(t))


def certificate(g, op):
    """Indices (i, j, k, l) with g = op(s_i, s_j) * op(s_k, s_l)."""
    pairs = {}
    for i in range(len(S)):
        for j in range(len(S)):
            pairs.setdefault(op(S[i], S[j]), (i, j))
    for k in range(len(S)):
        for l in range(len(S)):
            x = mul(g, inv(op(S[k], S[l])))
            if x in pairs:
                i, j = pairs[x]
                return (i, j, k, l)
    raise AssertionError(("no certificate", g))


def check_cert1(g, w):
    i, j, k, l = w
    return mul(mul(mul(inv(S[i]), S[j]), inv(S[k])), S[l]) == g


def check_cert2(g, w):
    i, j, k, l = w
    return mul(mul(mul(S[i], inv(S[j])), S[k]), inv(S[l])) == g


def certificates():
    cert1, cert2 = [], []
    for g in ALL:
        c1, c2 = certificate(g, form1), certificate(g, form2)
        assert check_cert1(g, c1), ("cert1 fails", g)
        assert check_cert2(g, c2), ("cert2 fails", g)
        cert1.append(c1)
        cert2.append(c2)
    return cert1, cert2


def haar_check():
    """BFS on the Haar graph: vertices (g, A) = index n, (g, B) = index 576 + n; (g, A) ~ (s g, B)."""
    index = {g: n for n, g in enumerate(ALL)}
    adj = [set() for _ in range(2 * N)]
    for g in ALL:
        for s in S:
            u = index[g]
            v = N + index[mul(s, g)]
            adj[u].add(v)
            adj[v].add(u)
    assert all(len(a) == len(S) for a in adj), "not 7-regular"
    color = [-1] * (2 * N)
    color[0] = 0
    queue = deque([0])
    while queue:
        x = queue.popleft()
        for y in adj[x]:
            if color[y] < 0:
                color[y] = 1 - color[x]
                queue.append(y)
            else:
                assert color[y] != color[x], "not bipartite"
    diameter = 0
    for src in range(2 * N):
        dist = [-1] * (2 * N)
        dist[src] = 0
        queue = deque([src])
        while queue:
            x = queue.popleft()
            for y in adj[x]:
                if dist[y] < 0:
                    dist[y] = dist[x] + 1
                    queue.append(y)
        assert min(dist) >= 0, "disconnected"
        diameter = max(diameter, max(dist))
    return 2 * N, diameter


def lean_list(ws):
    rows = []
    for t in range(0, len(ws), 10):
        rows.append("    " + ", ".join("(%d, %d, %d, %d)" % w for w in ws[t:t + 10]))
    return "[\n" + ",\n".join(rows) + "]"


def s_entries():
    return ",\n    ".join(
        "(permOf %d, Multiplicative.ofAdd (%d : ZMod 24))" % (PERM_INDEX[p], c) for p, c in S)


def s_comment():
    return "\n".join("  `%d`: `%s`, %d" % (i, list(p), c) for i, (p, c) in enumerate(S))


def cert_file(cert1, cert2):
    return f"""/- Generated by research/d5/make_haar_cert_1152.py. Do not edit by hand. -/
import BipartiteDD.Haar.S4Z24

/-! Covering certificates for the (7,5) Haar record on 1152 vertices, the Haar graph of `S_4 × Z_24`.
Entry `n` of `cert1` (resp. `cert2`) is a quadruple of indices into `sS` for the element `grpOf n`.
The checks `ok1`, `ok2` run over all `n < 576` by computation, and `cover1`, `cover2` give the
covering hypotheses of `Haar.Main`.

The connection set `sS` (index: one-line permutation, element of `Z_24`):
{s_comment()} -/

namespace BipartiteDD.Haar.S4Z24

open BipartiteDD.Haar

/-- The connection set `S` of the (7,5) record on 1152 vertices. -/
def sS : Fin 7 → Grp :=
  ![{s_entries()}]

/-- `S` as a finset. -/
def SS : Finset Grp := Finset.univ.image sS

theorem card_SS : SS.card = 7 := by decide +kernel

theorem sS_mem (i : Fin 7) : sS i ∈ SS :=
  Finset.mem_image_of_mem sS (Finset.mem_univ i)

set_option maxRecDepth 100000 in
/-- `grpOf n = s_i⁻¹ s_j s_k⁻¹ s_l`. -/
def cert1 : List (Fin 7 × Fin 7 × Fin 7 × Fin 7) := {lean_list(cert1)}

set_option maxRecDepth 100000 in
/-- `grpOf n = s_i s_j⁻¹ s_k s_l⁻¹`. -/
def cert2 : List (Fin 7 × Fin 7 × Fin 7 × Fin 7) := {lean_list(cert2)}

/-- The first certificate is right at index `n`. -/
def ok1 (n : ℕ) : Bool :=
  let w := cert1.getD n (0, 0, 0, 0)
  decide (grpOf n = (sS w.1)⁻¹ * sS w.2.1 * (sS w.2.2.1)⁻¹ * sS w.2.2.2)

/-- The second certificate is right at index `n`. -/
def ok2 (n : ℕ) : Bool :=
  let w := cert2.getD n (0, 0, 0, 0)
  decide (grpOf n = sS w.1 * (sS w.2.1)⁻¹ * sS w.2.2.1 * (sS w.2.2.2)⁻¹)

set_option maxRecDepth 100000 in
theorem ok1_all : (List.range 576).all ok1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ok2_all : (List.range 576).all ok2 = true := by decide +kernel

/-- Every element is `a⁻¹ b c⁻¹ d` with `a, b, c, d ∈ SS`. -/
theorem cover1 : ∀ g : Grp, ∃ a ∈ SS, ∃ b ∈ SS, ∃ c ∈ SS, ∃ d ∈ SS, g = a⁻¹ * b * c⁻¹ * d := by
  intro g
  obtain ⟨n, hn, rfl⟩ := exists_grpOf g
  have h := List.all_eq_true.mp ok1_all n (List.mem_range.mpr hn)
  simp only [ok1, decide_eq_true_eq] at h
  exact ⟨_, sS_mem _, _, sS_mem _, _, sS_mem _, _, sS_mem _, h⟩

/-- Every element is `a b⁻¹ c d⁻¹` with `a, b, c, d ∈ SS`. -/
theorem cover2 : ∀ g : Grp, ∃ a ∈ SS, ∃ b ∈ SS, ∃ c ∈ SS, ∃ d ∈ SS, g = a * b⁻¹ * c * d⁻¹ := by
  intro g
  obtain ⟨n, hn, rfl⟩ := exists_grpOf g
  have h := List.all_eq_true.mp ok2_all n (List.mem_range.mpr hn)
  simp only [ok2, decide_eq_true_eq] at h
  exact ⟨_, sS_mem _, _, sS_mem _, _, sS_mem _, _, sS_mem _, h⟩

end BipartiteDD.Haar.S4Z24
"""


def main():
    cert1, cert2 = certificates()
    n, diameter = haar_check()
    assert n == 1152 and diameter == 5, (n, diameter)
    (LEAN / "Cert1152.lean").write_text(cert_file(cert1, cert2))
    print("ok: 576 elements, both certificates checked, Haar graph on", n,
          "vertices, 7-regular, bipartite, diameter", diameter, "; wrote Cert1152.lean")
    return 0


if __name__ == "__main__":
    sys.exit(main())
