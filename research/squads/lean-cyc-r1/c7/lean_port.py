#!/usr/bin/env python3
"""Card c7 of squad lean-cyc-r1: a line-by-line Python port of the Boolean checks in
lean/BipartiteDD/Haar/CycLift/Lift.lean and Aut.lean, run with the exact arguments of each
data file's theorem (parsed from the .lean text) on the six CycLift files.

Nat semantics: `a - b` truncates at 0 and `x % 0 = x` (nsub, nmod). Bitwise operators are Python's,
which agree with Lean's &&&, |||, >>>, <<< on naturals. Lean's List.getD returns the default
outside the range. The piecewise definitions pi/piInv and the side lists are read from the file
text and evaluated through an AST that rewrites `-` and `%` into the Nat versions.
"""
import ast
import json
import random
import re
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
LEAN = ROOT / "lean" / "BipartiteDD" / "Haar" / "CycLift"
HERE = Path(__file__).resolve().parent
FILES = ["N3400", "N5706", "N30334", "N74066", "N192382", "N497042"]


# ---------- Nat semantics ----------
def nsub(a, b):
    return a - b if a >= b else 0


def nmod(a, b):
    return a % b if b != 0 else a


def getD(xs, i, dflt):
    return xs[i] if 0 <= i < len(xs) else dflt


def boolGetD(xs, i):
    return xs[i] if 0 <= i < len(xs) else False


# ---------- Lift.lean ----------
def rotR(m, beta, x):
    # ((x &&& (2 ^ m - 1)) >>> β ||| (x &&& (2 ^ m - 1)) <<< (m - β)) &&& (2 ^ m - 1)
    full = (1 << m) - 1
    a = x & full
    return ((a >> beta) | (a << nsub(m, beta))) & full


def stepM(m, b, outA, cur):
    # (List.range b).map fun w => (outA.getD w []).foldl (fun acc p => acc ||| rotR m p.2 (cur.getD p.1 0)) (cur.getD w 0)
    out = []
    for w in range(b):
        acc = getD(cur, w, 0)
        for p in getD(outA, w, []):
            acc = acc | rotR(m, p[1], getD(cur, p[0], 0))
        out.append(acc)
    return out


def levM(m, b, outA, u0, r):
    if r == 0:
        return [1 if w == u0 else 0 for w in range(b)]
    return stepM(m, b, outA, levM(m, b, outA, u0, r - 1))


def eccOK(m, b, D, outA):
    full = (1 << m) - 1
    return all(all((x & full) == full for x in levM(m, b, outA, u0, D)) for u0 in range(b))


def arcsOK(m, b, outA):
    return all(all((p[0] < b) and (p[1] < m) for p in getD(outA, w, [])) for w in range(b))


def symOK(m, b, outA):
    return all(
        all((w, nmod(nsub(m, p[1]), m)) in getD(outA, p[0], []) for p in getD(outA, w, []))
        for w in range(b)
    )


def degOK(d, b, outA):
    return all(len(getD(outA, w, [])) <= d for w in range(b))


def colOK(b, side, outA):
    return all(
        all(boolGetD(side, w) != boolGetD(side, p[0]) for p in getD(outA, w, []))
        for w in range(b)
    )


# ---------- Aut.lean ----------
def autOK(m, b, pi, mu, outA):
    return all(
        (pi(w) < b) and all((pi(p[0]), nmod(mu * p[1], m)) in getD(outA, pi(w), []) for p in getD(outA, w, []))
        for w in range(b)
    )


def invOK(m, b, pi, pinv, mu, mup):
    part = all((pinv(w) < b) and (pi(pinv(w)) == w) and (pinv(pi(w)) == w) for w in range(b))
    return part and (nmod(mu * mup, m) == nmod(1, m))


def orbL(pi, K, u):
    # | 0, _ => [] | K + 1, u => u :: orbL π K (π u)
    if K == 0:
        return []
    return [u] + orbL(pi, K - 1, pi(u))


def orbOK(b, K, pi, srcs):
    return all(any(w in orbL(pi, K, u0) for u0 in srcs) for w in range(b))


def eccSrcOK(m, b, D, outA, srcs):
    full = (1 << m) - 1
    return all(
        (u0 < b) and all((x & full) == full for x in levM(m, b, outA, u0, D))
        for u0 in srcs
    )


# ---------- reading the .lean text ----------
class NatTx(ast.NodeTransformer):
    def visit_BinOp(self, node):
        self.generic_visit(node)
        if isinstance(node.op, ast.Sub):
            return ast.Call(func=ast.Name("nsub", ast.Load()), args=[node.left, node.right], keywords=[])
        if isinstance(node.op, ast.Mod):
            return ast.Call(func=ast.Name("nmod", ast.Load()), args=[node.left, node.right], keywords=[])
        return node


def make_nat_fun(src):
    tree = ast.parse(src, mode="eval")
    tree = ast.fix_missing_locations(NatTx().visit(tree))
    code = compile(tree, "<lean-def>", "eval")
    g = {"__builtins__": {}, "nsub": nsub, "nmod": nmod}
    return lambda w: eval(code, g, {"w": w})


def parse_outA(text, name):
    head = f"def {name} : List (List (ℕ × ℕ)) := ["
    k = text.index(head)
    i = k + len(head) - 1  # index of the outer '['
    depth, j = 0, i
    while True:
        ch = text[j]
        if ch == "[":
            depth += 1
        elif ch == "]":
            depth -= 1
            if depth == 0:
                break
        j += 1
    inner = text[i + 1:j]
    assert re.fullmatch(r"[\s,]*", re.sub(r"\[[^\[\]]*\]", "", inner)), "unexpected text in outA"
    rows = []
    for mm in re.finditer(r"\[([^\[\]]*)\]", inner):
        body = mm[1]
        assert re.fullmatch(r"\s*(?:\(\s*\d+,\s*\d+\s*\)\s*,?\s*)*", body), body
        rows.append([(int(a), int(b)) for a, b in re.findall(r"\((\d+),\s*(\d+)\)", body)])
    return rows


def parse_side(text, name):
    head = f"def {name} : List Bool := "
    k = text.index(head)
    rhs = text[k + len(head):].split("\n\n", 1)[0].strip()
    if rhs.startswith("["):
        assert rhs.endswith("]")
        return [t == "true" for t in re.findall(r"\b(true|false)\b", rhs)]
    mm = re.fullmatch(r"\(List\.range (\d+)\)\.map fun w => decide \((\d+) ≤ w\)", rhs)
    assert mm, rhs
    return [w >= int(mm[2]) for w in range(int(mm[1]))]


def parse_def_fun(text, name):
    head = f"def {name} (w : ℕ) : ℕ := "
    k = text.index(head)
    rhs = text[k + len(head):].split("\n\n", 1)[0].strip()
    mm = re.fullmatch(r"if w < (\d+) then (.+?) else (.+)", rhs)
    assert mm, rhs
    K = int(mm[1])
    f_then, f_else = make_nat_fun(mm[2]), make_nat_fun(mm[3])
    return (lambda w: f_then(w) if w < K else f_else(w)), rhs


# ---------- one file ----------
def check_file(name):
    text = (LEAN / f"{name}.lean").read_text(encoding="utf-8")
    g = re.search(r"def G\d+ : SimpleGraph \(Fin (\d+)\) := liftGraph (\d+) (\d+) (outA\d+)", text)
    n, n2, m, outname = int(g[1]), int(g[2]), int(g[3]), g[4]
    assert n == n2
    outA = parse_outA(text, outname)
    b = len(outA)

    thm = re.search(r"theorem (G\d+)_isBipartiteDegDiam : IsBipartiteDegDiam (G\d+) (\d+) (\d+) :=", text)
    d, D = int(thm[3]), int(thm[4])
    call = text[thm.end():].split("\n\n", 1)[0]
    kind = "checks" if "isBipartiteDegDiam_of_checks" in call else "srcs"
    assert "isBipartiteDegDiam_of_srcs" in call or kind == "checks"
    named = dict(re.findall(r"\((\S+) := ([^()\s]+)\)", call))
    b_thm = int(named["b"])
    assert b_thm == b, (b_thm, b)
    side_name = re.search(r"\b(side\w+)\b", call)[1]
    side = parse_side(text, side_name)
    assert len(side) == b
    n_rfl = len(re.findall(r"\brfl\b", call))
    n_dec = len(re.findall(r"\(by decide\)", call))
    n_ker = len(re.findall(r"\(by decide \+kernel\)", call))
    assert n_rfl == 1 and n_dec == 1, (n_rfl, n_dec)
    assert n_ker == (5 if kind == "checks" else 8), n_ker

    R, Rm1 = {}, {}  # results at D, results at D-1 (must be false)
    R["hn_rfl(n=b*m)"] = n == b * m
    R["hm(0<m)"] = 0 < m
    R["arcsOK"] = arcsOK(m, b, outA)
    R["symOK"] = symOK(m, b, outA)
    R["degOK(d)"] = degOK(d, b, outA)
    R["colOK"] = colOK(b, side, outA)
    info = {"n": n, "m": m, "b": b, "d": d, "D": D, "kind": kind, "side": side_name}

    if kind == "checks":
        R["eccOK(D)"] = eccOK(m, b, D, outA)
        Rm1["eccOK(D-1)"] = eccOK(m, b, D - 1, outA)
        full = lambda r: eccOK(m, b, r, outA)
    else:
        srcs = [int(t) for t in re.search(r"\[([\d,\s]*)\]", call)[1].split(",") if t.strip()]
        pi, pi_rhs = parse_def_fun(text, named["π"])
        pinv, pinv_rhs = parse_def_fun(text, named["π'"])
        mu, mup, K = int(named["μ"]), int(named["μ'"]), int(named["K"])
        info.update({"srcs": srcs, "mu": mu, "mu_inv": mup, "K": K, "pi": pi_rhs, "pi_inv": pinv_rhs})
        R["autOK"] = autOK(m, b, pi, mu, outA)
        R["invOK"] = invOK(m, b, pi, pinv, mu, mup)
        R["orbOK"] = orbOK(b, K, pi, srcs)
        R["eccSrcOK(D)"] = eccSrcOK(m, b, D, outA, srcs)
        Rm1["eccSrcOK(D-1)"] = eccSrcOK(m, b, D - 1, outA, srcs)
        full = lambda r: eccSrcOK(m, b, r, outA, srcs)

    # smallest radius at which the literal eccOK / eccSrcOK check passes (monotone in r)
    first_full = next((r for r in range(0, D + 4) if full(r)), None)
    ok = all(R.values()) and not any(Rm1.values())
    return {"file": name, **info, "at_D": R, "at_D_minus_1": Rm1, "first_full_radius": first_full, "ok": ok}


def selftest_rotR(trials=4000):
    # Lean's testBit_rotR: bit y of rotR m β x is bit (y + β) % m of x, for y < m, β < m
    rng = random.Random(1)
    for _ in range(trials):
        m = rng.randint(1, 90)
        beta = rng.randrange(m)
        x = rng.getrandbits(m + 7)
        r = rotR(m, beta, x)
        assert r >> m == 0
        for y in range(m):
            assert ((r >> y) & 1) == ((x >> ((y + beta) % m)) & 1)
    m = 2731
    x = rng.getrandbits(m + 40)
    for beta in (0, 1, 33, 2400, 2730):
        r = rotR(m, beta, x)
        for y in rng.sample(range(m), 200):
            assert ((r >> y) & 1) == ((x >> ((y + beta) % m)) & 1)
    return True


def selftest_nat():
    assert nsub(3, 5) == 0 and nsub(5, 3) == 2 and nmod(7, 0) == 7 and nmod(7, 3) == 1
    f = make_nat_fun("(w - 29 + 1) % 29")
    assert f(29) == 1 and f(30) == 2 and f(3) == nmod(nsub(3, 29) + 1, 29)
    return True


def main():
    t0 = time.time()
    selftests = {"rotR_testBit_property": selftest_rotR(), "nat_helpers": selftest_nat()}
    results = [check_file(f) for f in FILES]
    score = sum(1 for r in results if r["ok"])
    out = {
        "card": "c7",
        "score": score,
        "valid": True,
        "selftests": selftests,
        "elapsed_s": round(time.time() - t0, 2),
        "results": results,
    }
    (HERE / "result.json").write_text(json.dumps(out, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    for r in results:
        bad = [k for k, v in r["at_D"].items() if not v] + [k for k, v in r["at_D_minus_1"].items() if v]
        print(
            f"{r['file']:9s} n={r['n']:6d} m={r['m']:5d} b={r['b']:3d} d={r['d']} D={r['D']:2d} "
            f"{r['kind']:6s} first_full_radius={r['first_full_radius']} ok={r['ok']} failed={bad}"
        )
    print(f"score={score}/6 selftests={selftests} elapsed={out['elapsed_s']}s")


if __name__ == "__main__":
    main()
