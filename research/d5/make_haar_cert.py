"""Lean files for the Haar records of diameter 5 whose group is Z_m x|_lam Z_k.

  python3 research/d5/make_haar_cert.py          (from the repository root)

Writes, under lean/BipartiteDD/Haar/:
  Cert2620.lean  the (9,5) record on 2620 vertices, group Z_131 x|_53 Z_10 (Z131.lean, hand-written);
  Z144.lean      the group Z_144 x|_25 Z_6 (copied from Z131.lean with the parameters changed);
  Cert1728.lean  the (8,5) record on 1728 vertices, over Z144.lean.

The group is the one of build_haar.py (`mul`). The connection set S is read from the solution file
(9,5) or from the "construction" field of the record JSON (8,5). For every element g, with index
n = enc g = m * y + x, a certificate lists indices (i, j, k, l) into S with

  cert1: g = s_i^-1 * s_j * s_k^-1 * s_l        (covers (S^-1 S)^2)
  cert2: g = s_i * s_j^-1 * s_k * s_l^-1        (covers (S S^-1)^2)

Lean re-checks every entry with `decide +kernel`; the certificates are not trusted.
"""
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LEAN = ROOT / "lean" / "BipartiteDD" / "Haar"


def load_9_5():
    rows = [list(map(int, l.split())) for l in open(ROOT / "research/d5/sols/h2_d9_N1310_m131_k10_l53.txt") if l.strip()]
    d, m, k, lam = rows[0]
    assert (d, m, k, lam) == (9, 131, 10, 53)
    return dict(M=m, K=k, LAM=lam, S=[tuple(r) for r in rows[1:]], d=d, n=2 * m * k, name="2620",
                ns="Z131", group_file=None)


def load_8_5():
    rec = json.load(open(ROOT / "records/bipartite_dd/d8D5/1728-d5-haar_d8_n1728.json"))
    c = rec["construction"]
    m, k = 144, 6
    lam = 25
    assert c["group"] == "Z_144 x|_25 Z_6"
    return dict(M=m, K=k, LAM=lam, S=[tuple(s) for s in c["S"]], d=8, n=2 * m * k, name="1728",
                ns="Z144", group_file="Z144")


def mul_fn(M, K, LAM):
    pw = [pow(LAM, j, M) for j in range(K)]

    def mul(g, h):
        (a, j), (b, l) = g, h
        return ((a + pw[j] * b) % M, (j + l) % K)

    def inv(g):
        a, j = g
        return ((-a * pw[(-j) % K]) % M, (-j) % K)

    return mul, inv


def witnesses(cfg):
    M, K, S = cfg["M"], cfg["K"], cfg["S"]
    mul, inv = mul_fn(M, K, cfg["LAM"])
    d = len(S)
    cert1, cert2 = [], []
    for n in range(M * K):
        g = (n % M, n // M)
        forms = {1: None, 2: None}
        for i in range(d):
            for j in range(d):
                for k in range(d):
                    for l in range(d):
                        if forms[1] is None:
                            p = mul(mul(mul(inv(S[i]), S[j]), inv(S[k])), S[l])
                            if p == g:
                                forms[1] = (i, j, k, l)
                        if forms[2] is None:
                            p = mul(mul(mul(S[i], inv(S[j])), S[k]), inv(S[l]))
                            if p == g:
                                forms[2] = (i, j, k, l)
        assert forms[1] is not None and forms[2] is not None, (cfg["name"], g)
        cert1.append(forms[1])
        cert2.append(forms[2])
    return cert1, cert2


def lean_list(ws):
    rows = []
    for t in range(0, len(ws), 10):
        rows.append("    " + ", ".join("(%d, %d, %d, %d)" % w for w in ws[t:t + 10]))
    return "[\n" + ",\n".join(rows) + "]"


def group_file(cfg, template):
    """The group file of `cfg`, from the hand-checked Z131 template by changing the parameters."""
    d, M, K, LAM = cfg["d"], cfg["M"], cfg["K"], cfg["LAM"]
    s_entries = ", ".join("⟨%d, %d⟩" % (x, y) for x, y in cfg["S"])
    text = template
    # the connection set block, from its doc comment up to the finset `S`
    lo = text.index("/-- The connection set")
    hi = text.index("/-- `S` as a finset. -/")
    block = (f"/-- The connection set `S` of the ({d},5) record on {cfg['n']} vertices, in the order of its "
             f"record file. -/\ndef s{d} : Fin {d} → Grp :=\n  ![{s_entries}]\n\n")
    text = text[:lo] + block + text[hi:]
    text = re.sub(r"\bs9\b", f"s{d}", text)
    text = re.sub(r"\bS9\b", f"S{d}", text)
    text = re.sub(r"card_S9", f"card_S{d}", text)
    text = re.sub(r"s9_mem", f"s{d}_mem", text)
    text = text.replace("Fin 9", f"Fin {d}")
    text = text.replace("namespace BipartiteDD.Haar.Z131", "namespace BipartiteDD.Haar.Z144")
    text = text.replace("end BipartiteDD.Haar.Z131", "end BipartiteDD.Haar.Z144")
    text = text.replace("ZMod 131", f"ZMod {M}").replace("ZMod 10", f"ZMod {K}")
    text = text.replace("53 ^", f"{LAM} ^").replace("53 ^", f"{LAM} ^")
    text = text.replace("Fintype.card Grp = 1310", f"Fintype.card Grp = {M * K}")
    lo = text.index("/-! The group")
    hi = text.index("namespace BipartiteDD.Haar.Z144")
    header = (f"/-! The group `Z_{M} ⋊ Z_{K}` of the ({d},5) record on {cfg['n']} vertices.\n\n"
              f"Elements are pairs `(x, y)` with `x ∈ ZMod {M}` and `y ∈ ZMod {K}`, with product\n"
              f"`(x, y) * (x', y') = (x + {LAM} ^ y.val * x', y + y')`. This is the product `mul` of\n"
              f"`research/d5/build_haar.py` (`pw[j] = {LAM} ^ j mod {M}`). The map `y ↦ {LAM} ^ y.val` is a\n"
              f"homomorphism `ZMod {K} → ZMod {M}` because `{LAM} ^ {K} = 1` in `ZMod {M}`; `tw_add` checks this\n"
              f"on all {K * K} pairs. -/\n\n")
    text = text[:lo] + header + text[hi:]
    text = text.replace("/-- Elements of `Z_131 ⋊ Z_10`. -/", f"/-- Elements of `Z_{M} ⋊ Z_{K}`. -/")
    text = text.replace(f"theorem card_S{d} : S{d}.card = 9", f"theorem card_S{d} : S{d}.card = {d}")
    text = text.replace("on all 100 pairs", f"on all {K * K} pairs")
    text = text.replace("tw_add : ∀ y z : ZMod 10", f"tw_add : ∀ y z : ZMod {K}")
    text = text.replace("for `y : ZMod 10`", f"for `y : ZMod {K}`")
    text = text.replace("def tw (y : ZMod 10)", f"def tw (y : ZMod {K})")
    return text


def cert_file(cfg, cert1, cert2):
    d, M, K = cfg["d"], cfg["M"], cfg["K"]
    ns, name = cfg["ns"], cfg["name"]
    return f"""/- Generated by research/d5/make_haar_cert.py. Do not edit by hand. -/
import BipartiteDD.Haar.{cfg["group_module"]}

/-! Covering certificates for the ({d},5) Haar record on {cfg["n"]} vertices. Entry `n` of `cert1` (resp.
`cert2`) is a quadruple of indices into `s{d}` for the element `dec n`. The checks `ok1`, `ok2` run
over all `n < {M * K}` by computation, and `cover1`, `cover2` give the covering hypotheses of
`Haar.Main`. -/

namespace BipartiteDD.Haar.{ns}

/-- The element with index `n`: `(n % {M}, n / {M})`. -/
def dec (n : ℕ) : Grp := ⟨(n : ZMod {M}), ((n / {M} : ℕ) : ZMod {K})⟩

/-- Index of an element, the inverse of `dec` on `n < {M * K}`. -/
def enc (g : Grp) : ℕ := g.y.val * {M} + g.x.val

set_option maxRecDepth 100000 in
/-- `dec n = s_i⁻¹ s_j s_k⁻¹ s_l`. -/
def cert1 : List (Fin {d} × Fin {d} × Fin {d} × Fin {d}) := {lean_list(cert1)}

set_option maxRecDepth 100000 in
/-- `dec n = s_i s_j⁻¹ s_k s_l⁻¹`. -/
def cert2 : List (Fin {d} × Fin {d} × Fin {d} × Fin {d}) := {lean_list(cert2)}

/-- The first certificate is right at index `n`. -/
def ok1 (n : ℕ) : Bool :=
  let w := cert1.getD n (0, 0, 0, 0)
  decide (dec n = (s{d} w.1)⁻¹ * s{d} w.2.1 * (s{d} w.2.2.1)⁻¹ * s{d} w.2.2.2)

/-- The second certificate is right at index `n`. -/
def ok2 (n : ℕ) : Bool :=
  let w := cert2.getD n (0, 0, 0, 0)
  decide (dec n = s{d} w.1 * (s{d} w.2.1)⁻¹ * s{d} w.2.2.1 * (s{d} w.2.2.2)⁻¹)

set_option maxRecDepth 100000 in
theorem ok1_all : (List.range {M * K}).all ok1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ok2_all : (List.range {M * K}).all ok2 = true := by decide +kernel

theorem dec_enc : ∀ g : Grp, dec (enc g) = g := by decide +kernel

theorem enc_lt : ∀ g : Grp, enc g < {M * K} := by decide +kernel

/-- Every element is `a⁻¹ b c⁻¹ d` with `a, b, c, d ∈ S`. -/
theorem cover1 : ∀ g : Grp, ∃ a ∈ S{d}, ∃ b ∈ S{d}, ∃ c ∈ S{d}, ∃ d ∈ S{d}, g = a⁻¹ * b * c⁻¹ * d := by
  intro g
  have h := List.all_eq_true.mp ok1_all (enc g) (List.mem_range.mpr (enc_lt g))
  simp only [ok1, decide_eq_true_eq, dec_enc] at h
  exact ⟨_, s{d}_mem _, _, s{d}_mem _, _, s{d}_mem _, _, s{d}_mem _, h⟩

/-- Every element is `a b⁻¹ c d⁻¹` with `a, b, c, d ∈ S`. -/
theorem cover2 : ∀ g : Grp, ∃ a ∈ S{d}, ∃ b ∈ S{d}, ∃ c ∈ S{d}, ∃ d ∈ S{d}, g = a * b⁻¹ * c * d⁻¹ := by
  intro g
  have h := List.all_eq_true.mp ok2_all (enc g) (List.mem_range.mpr (enc_lt g))
  simp only [ok2, decide_eq_true_eq, dec_enc] at h
  exact ⟨_, s{d}_mem _, _, s{d}_mem _, _, s{d}_mem _, _, s{d}_mem _, h⟩

end BipartiteDD.Haar.{ns}
"""


def main(which):
    template = (LEAN / "Z131.lean").read_text()
    if which in ("all", "2620"):
        cfg = load_9_5()
        cfg["group_module"] = "Z131"
        c1, c2 = witnesses(cfg)
        (LEAN / "Cert2620.lean").write_text(cert_file(cfg, c1, c2))
        print("wrote Cert2620.lean", len(c1), len(c2))
    if which in ("all", "1728"):
        cfg = load_8_5()
        cfg["group_module"] = "Z144"
        (LEAN / "Z144.lean").write_text(group_file(cfg, template))
        c1, c2 = witnesses(cfg)
        (LEAN / "Cert1728.lean").write_text(cert_file(cfg, c1, c2))
        print("wrote Z144.lean and Cert1728.lean", len(c1), len(c2))


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "all")
