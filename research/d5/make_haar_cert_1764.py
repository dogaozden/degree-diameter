"""Lean certificates for the (8,5) Haar record on 1764 vertices: the Haar graph of AGL(1,7) x Z_21.

  python3 research/d5/make_haar_cert_1764.py          (from the repository root)

Writes lean/BipartiteDD/Haar/Cert1764.lean. The group and the numbering of its elements are in
lean/BipartiteDD/Haar/AGL17Z21.lean (hand-written); this script follows the same conventions.

The brief (docs/lean-haar3-brief.md) writes an element as ((b, a), c): the map t -> a t + b on ZMod 7 with
a != 0, together with c in ZMod 21; (b1, a1)(b2, a2) = (a1 b2 + b1, a1 a2). Lean uses a = 3^y with y in
ZMod 6 (3 generates the units mod 7), so an element is (x, y, z) = (b, dlog_3 a, c) with product

  (x, y, z)(x', y', z') = (x + 3^y x', y + y', z + z').

The script checks that (b, a, c) -> (b, dlog a, c) is an isomorphism (a bijection preserving products), and
that the Haar graph has diameter 5 in both models. Index n < 882 is the element (n % 7, n // 7 % 6, n // 42).

For every n, a certificate lists indices (i, j, k, l) into the connection set S with

  cert1: g = s_i^-1 * s_j * s_k^-1 * s_l        (covers (S^-1 S)^2)
  cert2: g = s_i * s_j^-1 * s_k * s_l^-1        (covers (S S^-1)^2)

Lean re-checks every entry with `decide +kernel`; the certificates are not trusted.
"""
import sys
from collections import deque
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LEAN = ROOT / "lean" / "BipartiteDD" / "Haar"

N = 882
# Connection set of the brief: ((b, a), c).
S_BRIEF = [((0, 1), 0), ((0, 4), 5), ((6, 6), 18), ((6, 5), 6),
           ((2, 4), 1), ((2, 2), 16), ((4, 5), 12), ((2, 6), 15)]
DLOG = {pow(3, y, 7): y for y in range(6)}
assert sorted(DLOG) == [1, 2, 3, 4, 5, 6]


def mul_brief(g, h):
    ((b1, a1), c1), ((b2, a2), c2) = g, h
    return (((a1 * b2 + b1) % 7, (a1 * a2) % 7), (c1 + c2) % 21)


def to_model(g):
    (b, a), c = g
    return (b, DLOG[a], c)


# Model: (x, y, z) with product (x + 3^y x', y + y', z + z').
def mul(g, h):
    (x, y, z), (x2, y2, z2) = g, h
    return ((x + pow(3, y, 7) * x2) % 7, (y + y2) % 6, (z + z2) % 21)


def inv(g):
    x, y, z = g
    return ((-pow(3, (-y) % 6, 7) * x) % 7, (-y) % 6, (-z) % 21)


ONE = (0, 0, 0)
S = [to_model(s) for s in S_BRIEF]


def elem(n):
    """The element with index n < 882."""
    return (n % 7, n // 7 % 6, n // 42)


ALL = [elem(n) for n in range(N)]
assert len(set(ALL)) == N
assert len(set(S)) == 8


def check_iso():
    brief = [((b, a), c) for b in range(7) for a in range(1, 7) for c in range(21)]
    assert len(brief) == N and len({to_model(g) for g in brief}) == N
    for g in brief:
        for h in brief:
            assert to_model(mul_brief(g, h)) == mul(to_model(g), to_model(h))
    for g in ALL:
        assert mul(g, inv(g)) == ONE and mul(inv(g), g) == ONE


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


def haar_check(elems, s_set, mulf, expected):
    """BFS on the Haar graph: (g, A) = index n, (g, B) = index N + n; (g, A) ~ (s g, B)."""
    index = {g: n for n, g in enumerate(elems)}
    adj = [set() for _ in range(2 * N)]
    for g in elems:
        for s in s_set:
            u = index[g]
            v = N + index[mulf(s, g)]
            adj[u].add(v)
            adj[v].add(u)
    assert all(len(a) == len(s_set) for a in adj), "not regular of the expected degree"
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
    assert 2 * N == expected and diameter == 5, (2 * N, diameter)
    return diameter


def lean_list(ws):
    rows = []
    for t in range(0, len(ws), 10):
        rows.append("    " + ", ".join("(%d, %d, %d, %d)" % w for w in ws[t:t + 10]))
    return "[\n" + ",\n".join(rows) + "]"


def s_entries():
    return ",\n    ".join("⟨%d, %d, %d⟩" % s for s in S)


def cert_file(cert1, cert2):
    return f"""/- Generated by research/d5/make_haar_cert_1764.py. Do not edit by hand. -/
import BipartiteDD.Haar.AGL17Z21

/-! Covering certificates for the (8,5) Haar record on 1764 vertices, the Haar graph of `AGL(1,7) × Z_21`.
Entry `n` of `cert1` (resp. `cert2`) is a quadruple of indices into `sS` for the element `grpOf n`.
The checks `ok1`, `ok2` run over all `n < 882` by computation, and `cover1`, `cover2` give the
covering hypotheses of `Haar.Main`. -/

namespace BipartiteDD.Haar.AGL17Z21

open BipartiteDD.Haar

/-- The connection set `S` of the (8,5) record on 1764 vertices, as triples `(x, y, z)`: the elements
`((b, a), c)` of `docs/lean-haar3-brief.md` with `x = b`, `a = 3 ^ y`, `z = c`. -/
def sS : Fin 8 → Grp :=
  ![{s_entries()}]

/-- `S` as a finset. -/
def SS : Finset Grp := Finset.univ.image sS

theorem card_SS : SS.card = 8 := by decide +kernel

theorem sS_mem (i : Fin 8) : sS i ∈ SS :=
  Finset.mem_image_of_mem sS (Finset.mem_univ i)

set_option maxRecDepth 100000 in
/-- `grpOf n = s_i⁻¹ s_j s_k⁻¹ s_l`. -/
def cert1 : List (Fin 8 × Fin 8 × Fin 8 × Fin 8) := {lean_list(cert1)}

set_option maxRecDepth 100000 in
/-- `grpOf n = s_i s_j⁻¹ s_k s_l⁻¹`. -/
def cert2 : List (Fin 8 × Fin 8 × Fin 8 × Fin 8) := {lean_list(cert2)}

/-- The first certificate is right at index `n`. -/
def ok1 (n : ℕ) : Bool :=
  let w := cert1.getD n (0, 0, 0, 0)
  decide (grpOf n = (sS w.1)⁻¹ * sS w.2.1 * (sS w.2.2.1)⁻¹ * sS w.2.2.2)

/-- The second certificate is right at index `n`. -/
def ok2 (n : ℕ) : Bool :=
  let w := cert2.getD n (0, 0, 0, 0)
  decide (grpOf n = sS w.1 * (sS w.2.1)⁻¹ * sS w.2.2.1 * (sS w.2.2.2)⁻¹)

set_option maxRecDepth 100000 in
theorem ok1_all : (List.range 882).all ok1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ok2_all : (List.range 882).all ok2 = true := by decide +kernel

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

end BipartiteDD.Haar.AGL17Z21
"""


def main():
    check_iso()
    brief_all = [((b, a), c) for b in range(7) for a in range(1, 7) for c in range(21)]
    haar_check(brief_all, S_BRIEF, mul_brief, 1764)   # the brief's model
    cert1, cert2 = certificates()
    d = haar_check(ALL, S, mul, 1764)                  # the Lean model
    (LEAN / "Cert1764.lean").write_text(cert_file(cert1, cert2))
    print("ok: 882 elements, both certificates checked, Haar graph on 1764 vertices, 8-regular, "
          "bipartite, diameter", d, "(brief's model and Lean model); wrote Cert1764.lean")
    return 0


if __name__ == "__main__":
    sys.exit(main())
