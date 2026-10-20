"""Lean certificates for the (9,5) Haar record on 2662 vertices: the Haar graph of the Heisenberg group mod 11.

  python3 research/d5/make_haar_cert_2662.py          (from the repository root)

Writes lean/BipartiteDD/Haar/Cert2662.lean. The group and the numbering of its elements are in
lean/BipartiteDD/Haar/Heis11.lean (hand-written); this script follows the same conventions:

  (a, b, c) is the matrix [[1, a, c], [0, 1, b], [0, 0, 1]] mod 11, with
  (a, b, c)(a', b', c') = (a + a', b + b', c + c' + a b').
  Index n < 1331 is the element (n // 121, n // 11 % 11, n % 11).

The connection set is the one of docs/lean-haar3-brief.md (research/d5/graphs/haar_d9_n2662.json). For every n,
a certificate lists indices (i, j, k, l) into S with

  cert1: g = s_i^-1 * s_j * s_k^-1 * s_l        (covers (S^-1 S)^2)
  cert2: g = s_i * s_j^-1 * s_k * s_l^-1        (covers (S S^-1)^2)

Before writing, the script re-checks every certificate and runs a breadth-first search on the Haar graph
(edges (g, A) ~ (s g, B)): 9-regular, bipartite, 2662 vertices, diameter 5. Lean re-checks every entry with
`decide +kernel`; the certificates are not trusted.
"""
import sys
from collections import deque
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LEAN = ROOT / "lean" / "BipartiteDD" / "Haar"

N = 1331
# Connection set of the brief: (a, b, c).
S = [(0, 0, 0), (8, 6, 10), (7, 9, 3), (10, 1, 8), (4, 4, 5), (5, 5, 8), (6, 5, 4), (1, 0, 9), (6, 10, 8)]


def mul(g, h):
    (a, b, c), (a2, b2, c2) = g, h
    return ((a + a2) % 11, (b + b2) % 11, (c + c2 + a * b2) % 11)


def inv(g):
    a, b, c = g
    return ((-a) % 11, (-b) % 11, (-c + a * b) % 11)


ONE = (0, 0, 0)


def elem(n):
    """The element with index n < 1331."""
    return (n // 121, n // 11 % 11, n % 11)


ALL = [elem(n) for n in range(N)]
assert len(set(ALL)) == N
assert len(set(S)) == 9


def check_group():
    for g in ALL:
        assert mul(g, inv(g)) == ONE and mul(inv(g), g) == ONE and mul(g, ONE) == g == mul(ONE, g)
    for g in ALL[::7]:
        for h in ALL[::5]:
            for k in ALL[::11]:
                assert mul(mul(g, h), k) == mul(g, mul(h, k))


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
    return f"""/- Generated by research/d5/make_haar_cert_2662.py. Do not edit by hand. -/
import BipartiteDD.Haar.Heis11

/-! Covering certificates for the (9,5) Haar record on 2662 vertices, the Haar graph of the Heisenberg group mod 11.
Entry `n` of `cert1` (resp. `cert2`) is a quadruple of indices into `sS` for the element `grpOf n`.
The checks `ok1`, `ok2` run over all `n < 1331` by computation, and `cover1`, `cover2` give the
covering hypotheses of `Haar.Main`. -/

namespace BipartiteDD.Haar.Heis11

open BipartiteDD.Haar

/-- The connection set `S` of the (9,5) record on 2662 vertices, as triples `(a, b, c)` in the
order of `docs/lean-haar3-brief.md`. -/
def sS : Fin 9 → Grp :=
  ![{s_entries()}]

/-- `S` as a finset. -/
def SS : Finset Grp := Finset.univ.image sS

theorem card_SS : SS.card = 9 := by decide +kernel

theorem sS_mem (i : Fin 9) : sS i ∈ SS :=
  Finset.mem_image_of_mem sS (Finset.mem_univ i)

set_option maxRecDepth 100000 in
/-- `grpOf n = s_i⁻¹ s_j s_k⁻¹ s_l`. -/
def cert1 : List (Fin 9 × Fin 9 × Fin 9 × Fin 9) := {lean_list(cert1)}

set_option maxRecDepth 100000 in
/-- `grpOf n = s_i s_j⁻¹ s_k s_l⁻¹`. -/
def cert2 : List (Fin 9 × Fin 9 × Fin 9 × Fin 9) := {lean_list(cert2)}

/-- The first certificate is right at index `n`. -/
def ok1 (n : ℕ) : Bool :=
  let w := cert1.getD n (0, 0, 0, 0)
  decide (grpOf n = (sS w.1)⁻¹ * sS w.2.1 * (sS w.2.2.1)⁻¹ * sS w.2.2.2)

/-- The second certificate is right at index `n`. -/
def ok2 (n : ℕ) : Bool :=
  let w := cert2.getD n (0, 0, 0, 0)
  decide (grpOf n = sS w.1 * (sS w.2.1)⁻¹ * sS w.2.2.1 * (sS w.2.2.2)⁻¹)

set_option maxRecDepth 100000 in
theorem ok1_all : (List.range 1331).all ok1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ok2_all : (List.range 1331).all ok2 = true := by decide +kernel

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

end BipartiteDD.Haar.Heis11
"""


def main():
    check_group()
    cert1, cert2 = certificates()
    d = haar_check(ALL, S, mul, 2662)
    (LEAN / "Cert2662.lean").write_text(cert_file(cert1, cert2))
    print("ok: 1331 elements, both certificates checked, Haar graph on 2662 vertices, 9-regular, "
          "bipartite, diameter", d, "; wrote Cert2662.lean")
    return 0


if __name__ == "__main__":
    sys.exit(main())
