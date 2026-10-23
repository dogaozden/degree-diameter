"""Certificate generator for the Delta7*D8 record 95,760 = Haar graph of G = PSL(2,19) x Z14 with the set S of
research/frontier/sols/d7D8_psl_19_14_orb3_s1.txt.

Group conventions (mirrored exactly by lean/BipartiteDD/Haar/D7D8/PSL19.lean):
  PSL(2,19) elements are matrices [[a,b],[c,d]] over Z/19 with det 1 modulo +-1.  The representative is the one with
  pos(a,c): (a if c == 0 else c) <= 9.  Product: matrix product, then canon (negate if not pos).
  Numbering: c == 0 -> (a-1)*19 + b (a in 1..9); c != 0 -> 171 + ((c-1)*19 + a)*19 + d (c in 1..9); b = (ad-1)/c.
  G = PSL x Z14 (direct), element index n = pIdx*14 + z.

Covering conditions for the Haar graph H(G,S) to have diameter <= 8 (checked here, then used in Lean):
  AA: every g = (a1^-1 b1)(a2^-1 b2)(a3^-1 b3)(a4^-1 b4)            (A-A distance <= 8)
  BB: every g = (a1 b1^-1)(a2 b2^-1)(a3 b3^-1)(a4 b4^-1)            (B-B distance <= 8)
  AB: every g = a (a1^-1 b1)(a2^-1 b2)(a3^-1 b3)                     (A-B distance <= 7)
Codes: AA and BB use 8 digits d0..d7 (S-indices), AB uses 7 digits d0..d6, code = sum d_k 7^k.

Usage: python3 gen_d7D8b.py SOL [CHUNK] [OUTDIR]   -- writes Gens.lean and Cert{AA,AB,BB}{k}.lean (OUTDIR default lean/...).
"""
import os
import re
import sys

P = 19
Q14 = 14
K_SMALL = 7


def inv19(x):
    return pow(x, P - 2, P)


def pos(a, c):
    return (a if c == 0 else c) <= 9


def canon(a, b, c, d):
    if pos(a, c):
        return (a, b, c, d)
    return ((-a) % P, (-b) % P, (-c) % P, (-d) % P)


def mul(g, h):
    a, b, c, d, z = g
    e, f, k, l, w = h
    m = canon((a * e + b * k) % P, (a * f + b * l) % P, (c * e + d * k) % P, (c * f + d * l) % P)
    return m + ((z + w) % Q14,)


def inv(g):
    a, b, c, d, z = g
    return canon(d, (-b) % P, (-c) % P, a) + ((-z) % Q14,)


ONE = (1, 0, 0, 1, 0)


def pidx(a, b, c, d):
    if c == 0:
        assert 1 <= a <= 9
        return (a - 1) * 19 + b
    assert 1 <= c <= 9
    return 171 + ((c - 1) * 19 + a) * 19 + d


def quad(n):
    if n < 171:
        a = n // 19 + 1
        return (a, n % 19, 0, inv19(a))
    m = n - 171
    c = m // 361 + 1
    a = (m // 19) % 19
    d = m % 19
    b = ((a * d - 1) * inv19(c)) % P
    return (a, b, c, d)


def check_numbering():
    seen = set()
    for n in range(3420):
        a, b, c, d = quad(n)
        assert (a * d - b * c) % P == 1 and pos(a, c), n
        assert canon(a, b, c, d) == (a, b, c, d)
        assert pidx(a, b, c, d) == n, n
        seen.add((a, b, c, d))
    assert len(seen) == 3420


def parse_sol(path):
    lines = [ln for ln in open(path).read().split("\n") if ln.strip()]
    head = lines[0].split()
    assert head[2:4] == ["psl", "19"] and head[4] == "n" and head[5] == "14", head
    S = []
    for ln in lines[1:8]:
        m = re.fullmatch(r"\s*\d+\s+mat\((\d+),(\d+),(\d+),(\d+)\)\s+z=(\d+)\s*", ln)
        a, b, c, d, z = map(int, m.groups())
        assert (a * d - b * c) % P == 1
        S.append(canon(a % P, b % P, c % P, d % P) + (z % Q14,))
    assert len(S) == 7 and len(set(S)) == 7
    assert S[0] == ONE
    return S


def bfs(gens_pairs, depth=4):
    """gens_pairs: dict element -> pair (i,j); returns list of dicts (level k: element -> word of k pairs)."""
    levels = [{ONE: ()}]
    for _ in range(depth):
        nxt = {}
        for g, w in levels[-1].items():
            for p, pr in gens_pairs.items():
                x = mul(p, g)
                if x not in nxt:
                    nxt[x] = (pr,) + w
        levels.append(nxt)
    return levels


def main():
    sol = sys.argv[1]
    chunk = int(sys.argv[2]) if len(sys.argv) > 2 else 4788
    outdir = sys.argv[3] if len(sys.argv) > 3 else os.path.join(
        os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "lean", "BipartiteDD", "Haar", "D7D8b")
    check_numbering()
    S = parse_sol(sol)
    Sinv = [inv(s) for s in S]

    # AA: P_AA = { S_i^-1 S_j }, words of exact length 4 as pairs (i, j)
    PAA = {}
    for i in range(7):
        for j in range(7):
            PAA.setdefault(mul(Sinv[i], S[j]), (i, j))
    LAA = bfs(PAA, 4)
    # BB: P_BB = { S_i S_j^-1 }
    PBB = {}
    for i in range(7):
        for j in range(7):
            PBB.setdefault(mul(S[i], Sinv[j]), (i, j))
    LBB = bfs(PBB, 4)

    NG = 3420 * 14
    def gidx(g):
        return pidx(*g[:4]) * 14 + g[4]

    def elem(n):
        return quad(n // 14) + (n % 14,)

    # every group element n: find codes
    codeAA, codeAB, codeBB = [0] * NG, [0] * NG, [0] * NG
    pow7 = [7 ** k for k in range(8)]
    L4 = LAA[4]
    assert len(L4) == NG, ("AA does not cover G", len(L4))
    L4B = LBB[4]
    assert len(L4B) == NG, ("BB does not cover G", len(L4B))
    L3 = LAA[3]
    for n in range(NG):
        g = elem(n)
        assert gidx(g) == n
        w = L4[g]
        digs = [x for pr in w for x in pr]
        codeAA[n] = sum(d * pow7[k] for k, d in enumerate(digs))
        # check the word product exactly as Lean will: (S_d0)^-1 S_d1 (S_d2^-1 S_d3)...
        acc = ONE
        for k in range(0, 8, 2):
            acc = mul(acc, mul(Sinv[digs[k]], S[digs[k + 1]]))
        assert acc == g, n
        wb = LBB[4][g]
        digb = [x for pr in wb for x in pr]
        codeBB[n] = sum(d * pow7[k] for k, d in enumerate(digb))
        acc = ONE
        for k in range(0, 8, 2):
            acc = mul(acc, mul(S[digb[k]], Sinv[digb[k + 1]]))
        assert acc == g, ("BB", n)
        # AB: x = S_i * w, w in L3 (3 pairs)
        found = None
        for i in range(7):
            w = L3.get(mul(Sinv[i], g))
            if w is not None:
                found = (i, w)
                break
        assert found is not None, ("AB", n)
        i, w = found
        digab = [i] + [x for pr in w for x in pr]
        codeAB[n] = sum(d * pow7[k] for k, d in enumerate(digab))
        acc = S[i]
        for k in range(1, 7, 2):
            acc = mul(acc, mul(Sinv[digab[k]], S[digab[k + 1]]))
        assert acc == g, ("AB word", n)

    os.makedirs(outdir, exist_ok=True)
    K = NG // chunk
    assert K * chunk == NG
    write_gens(os.path.join(outdir, "Gens.lean"), S)
    for name, codes in (("AA", codeAA), ("AB", codeAB), ("BB", codeBB)):
        for k in range(K):
            write_chunk(os.path.join(outdir, f"Cert{name}{k}.lean"), name, k, chunk,
                        codes[k * chunk:(k + 1) * chunk])
    write_cover(os.path.join(outdir, "Cover.lean"), K, chunk)
    print("all covering words verified:", NG, "elements; K =", K, "chunk =", chunk)


def write_cover(path, K, length):
    imports = "\n".join(f"import BipartiteDD.Haar.D7D8b.Cert{name}{k}"
                         for name in ("AA", "AB", "BB") for k in range(K))
    blocks = []
    for name in ("AA", "AB", "BB"):
        cases = "\n".join(f"  | {k} => cert{name}{k}" for k in range(K))
        oks = "\n".join(f"  · exact ok{name}{k}" for k in range(K))
        blocks.append(f"""def chunk{name} : ℕ → List ℕ
{cases}
  | _ => []

theorem chunk{name}_ok : ∀ k < {K}, chkList chk{name} (k * {length}) (chunk{name} k) = true := by
  intro k hk
  interval_cases k
{oks}

theorem chunk{name}_len : ∀ k < {K}, (chunk{name} k).length = {length} := by
  intro k hk
  interval_cases k <;> decide +kernel

theorem cov{name}_code (n : ℕ) (hn : n < {K * length}) :
    chk{name} n ((chunk{name} (n / {length})).getD (n % {length}) 0) = true := by
  have hk : n / {length} < {K} := by omega
  have h := chkList_spec chk{name} _ _ (chunk{name}_ok (n / {length}) hk) (n % {length})
    (by rw [chunk{name}_len _ hk]; omega)
  have e : n / {length} * {length} + n % {length} = n := by omega
  rw [e] at h
  exact h
""")
    body = "\n".join(blocks)
    text = f"""/- Generated by research/lean-haarD/d7D8b/gen_d7D8b.py. Do not edit by hand. -/
import Mathlib.Tactic.IntervalCases
{imports}

/-! The covering codes of `G`, stage by stage (`K = {K}` stages of `{length}` codes each), as chunk lists and the
statements that every index `n < {K * length}` has a covering word. -/

namespace BipartiteDD.Haar.D7D8b

{body}
end BipartiteDD.Haar.D7D8b
"""
    open(path, "w").write(text)


def lean_elem(g):
    a, b, c, d, z = g
    return f"(⟨{a}, {b}, {c}, {d}, by decide, by decide⟩, Multiplicative.ofAdd ({z} : ZMod 14))"


def write_gens(path, S):
    body = ",\n    ".join(lean_elem(g) for g in S)
    text = f"""/- Generated by research/lean-haarD/d7D8b/gen_d7D8b.py. Do not edit by hand. -/
import BipartiteDD.Haar.D7D8b.Base

/-! The seven generators `S` of the Delta7*D8 record (`d7D8_psl_19_14_orb3_s1`), as elements of
`PSL(2,19) × ZMod 14` in the normal form of `PSL19`. -/

namespace BipartiteDD.Haar.D7D8b

open BipartiteDD.Haar.PSL19

/-- The generators, indexed `0 … 6`; index `0` is the identity. -/
def sGl : List G :=
  [{body}]

end BipartiteDD.Haar.D7D8b
"""
    open(path, "w").write(text)


def write_chunk(path, name, k, length, codes):
    tokens = [str(c) for c in codes]
    lines = [", ".join(tokens[i:i + 24]) for i in range(0, len(tokens), 24)]
    body = ",\n    ".join(lines)
    text = f"""/- Generated by research/lean-haarD/d7D8b/gen_d7D8b.py. Do not edit by hand. -/
import BipartiteDD.Haar.D7D8b.Check

/-! Stage {name}{k}: covering codes for the group elements `n ∈ [{k * length}, {(k + 1) * length})`
(`n = pIdx * 14 + z`), checked by `decide +kernel`. -/

namespace BipartiteDD.Haar.D7D8b

set_option maxRecDepth 100000 in
/-- Codes of `{name}`, for `n` from `{k * length}`. -/
def cert{name}{k} : List ℕ :=
    [{body}]

set_option maxRecDepth 100000 in
theorem ok{name}{k} : chkList chk{name} {k * length} cert{name}{k} = true := by decide +kernel

end BipartiteDD.Haar.D7D8b
"""
    open(path, "w").write(text)


if __name__ == "__main__":
    main()
