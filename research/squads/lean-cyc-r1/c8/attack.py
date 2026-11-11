#!/usr/bin/env python3
"""c8: soundness attack on eccOK (lean/BipartiteDD/Haar/CycLift/Lift.lean), using mutants of outA3400.

Python port (Nat semantics, literal) of rotR, stepM, levM, eccOK, arcsOK, symOK, degOK.
Mutants keep arcsOK and symOK: every change is made to a base edge {a,c} with voltage beta
(arc a->c with beta, arc c->a with (m-beta)%m), so an arc and its reverse always move together.
Real diameter: exact BFS from every vertex of the lift (C helper bfs_diam.c, compiled here).
"""
import json
import os
import random
import re
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = "/home/user/degree-diameter/lean/BipartiteDD/Haar/CycLift/N3400.lean"
SRC = os.path.join(HERE, "bfs_diam.c")
BIN = os.path.join(HERE, "bfs_diam")
OUT = os.path.join(HERE, "results.json")

M, B, D, DEG = 170, 20, 13, 3      # N3400: lift of a 20-vertex base by Z_170, degree 3, diameter 13
N = B * M                          # 3400
CAP = 40                           # radius cap for the exact first-full-radius computation
N_RANDOM = 2000
SEED = 20260111
SAMPLE_FAILS = 400                 # failing mutants also checked against the real diameter (sample)


# ---------- parsing ----------
def parse_outA(txt):
    i = txt.index("def outA3400")
    j = txt.index("/-- A proper 2-colouring", i)
    rows = re.findall(r"\[((?:\(\d+, \d+\)(?:, )?)+)\]", txt[i:j])
    return [[(int(a), int(b)) for a, b in re.findall(r"\((\d+), (\d+)\)", r)] for r in rows]


# ---------- literal port of Lift.lean ----------
def getd(lst, i, dflt):
    """Lean List.getD: element i, or dflt when i is out of range."""
    return lst[i] if 0 <= i < len(lst) else dflt


def rotR(m, beta, x):
    # ((x &&& (2^m-1)) >>> beta ||| (x &&& (2^m-1)) <<< (m - beta)) &&& (2^m-1), with Nat truncation
    full = (1 << m) - 1
    y = x & full
    return ((y >> beta) | (y << max(0, m - beta))) & full


def stepM(m, b, outA, cur):
    res = []
    for w in range(b):
        acc = getd(cur, w, 0)
        for (u, beta) in getd(outA, w, []):
            acc = acc | rotR(m, beta, getd(cur, u, 0))
        res.append(acc)
    return res


def levM(m, b, outA, u0, r):
    cur = [1 if w == u0 else 0 for w in range(b)]
    for _ in range(r):
        cur = stepM(m, b, outA, cur)
    return cur


def eccOK(m, b, Dd, outA):
    full = (1 << m) - 1
    return all(all((x & full) == full for x in levM(m, b, outA, u0, Dd)) for u0 in range(b))


def arcsOK(m, b, outA):
    return all(p[0] < b and p[1] < m for w in range(b) for p in getd(outA, w, []))


def symOK(m, b, outA):
    return all((w, (m - p[1]) % m) in getd(outA, p[0], []) for w in range(b) for p in getd(outA, w, []))


def degOK(d, b, outA):
    return all(len(getd(outA, w, [])) <= d for w in range(b))


# ---------- exact quantities ----------
def mask_diam(m, b, outA, cap=CAP):
    """Smallest Dd with eccOK m b Dd outA = true (levM is monotone), or None if above cap."""
    full = (1 << m) - 1
    worst = 0
    for u0 in range(b):
        cur = [1 if w == u0 else 0 for w in range(b)]
        found = None
        for r in range(cap + 1):
            if all((x & full) == full for x in cur):
                found = r
                break
            cur = stepM(m, b, outA, cur)
        if found is None:
            return None
        worst = max(worst, found)
    return worst


def lift_edges(m, b, outA):
    """Undirected simple edge set of liftGraph (graphOf nbrs): fromRel symmetrises and drops loops."""
    n = b * m
    es = set()
    for v in range(n):
        w, x = divmod(v, m)
        for (u, beta) in getd(outA, w, []):
            t = (u * m + (x + beta) % m) % n
            if t != v:
                es.add((v, t) if v < t else (t, v))
    return n, es


def real_diam(m, b, outA):
    """Exact diameter of the lift by BFS from every vertex (C helper). None if disconnected."""
    n, es = lift_edges(m, b, outA)
    lines = ["%d %d" % (n, len(es))] + ["%d %d" % e for e in sorted(es)]
    r = subprocess.run([BIN], input="\n".join(lines) + "\n", capture_output=True, text=True, check=True)
    d = int(r.stdout.strip())
    return None if d < 0 else d


def build_bin():
    if not os.path.exists(BIN) or os.path.getmtime(BIN) < os.path.getmtime(SRC):
        subprocess.run(["gcc", "-O2", "-Wall", "-o", BIN, SRC], check=True)


# ---------- base graph as undirected voltage edges ----------
def edges_from_outA(outA):
    return [[w, u, beta] for w, row in enumerate(outA) for (u, beta) in row if u > w]


def outA_from_E(E):
    out = [[] for _ in range(B)]
    for a, c, beta in E:
        out[a].append((c, beta))
        out[c].append((a, (M - beta) % M))
    return out


def op_volt(E, rng):
    i = rng.randrange(len(E))
    E2 = [list(e) for e in E]
    nb = rng.randrange(M)
    if nb == E2[i][2]:
        nb = (nb + 1) % M
    E2[i][2] = nb
    return E2, "volt edge%d->%d" % (i, nb)


def op_switch(E, rng):
    for _ in range(200):
        i, j = rng.sample(range(len(E)), 2)
        a, c1, b1 = E[i]
        c, d, b2 = E[j]
        if a == d or c == c1:          # would create a loop
            continue
        E2 = [list(e) for e in E]
        if rng.random() < 0.5:
            b1, b2 = rng.randrange(M), rng.randrange(M)
        E2[i] = [a, d, b1]
        E2[j] = [c, c1, b2]
        return E2, "switch edges %d,%d" % (i, j)
    return None


def op_rewire(E, rng):
    i = rng.randrange(len(E))
    a, c1, beta = E[i]
    cands = [x for x in range(B) if x != a and x != c1]
    c = rng.choice(cands)
    E2 = [list(e) for e in E]
    E2[i] = [a, c, beta]
    return E2, "rewire edge%d end %d->%d" % (i, c1, c)


def random_mutant(E0, rng):
    E = E0
    descs = []
    for _ in range(rng.randint(1, 4)):
        r = rng.random()
        res = op_volt(E, rng) if r < 0.5 else (op_switch(E, rng) if r < 0.8 else op_rewire(E, rng))
        if res is None:
            continue
        E, dsc = res
        descs.append(dsc)
    return E, "; ".join(descs)


# ---------- evaluation ----------
def evaluate(E, desc, want_real, want_mask):
    outA = outA_from_E(E)
    rec = {"desc": desc, "valid": arcsOK(M, B, outA) and symOK(M, B, outA),
           "degOK3": degOK(DEG, B, outA)}
    rec["eccOK13"] = eccOK(M, B, D, outA)
    if want_mask:
        rec["mask_diam"] = mask_diam(M, B, outA)
    if want_real:
        rec["real"] = real_diam(M, B, outA)
    return rec


def main():
    t0 = time.time()
    build_bin()
    # self-tests of the binary
    assert subprocess.run([BIN], input="3 2\n0 1\n1 2\n", capture_output=True, text=True).stdout.strip() == "2"
    assert subprocess.run([BIN], input="3 1\n0 1\n", capture_output=True, text=True).stdout.strip() == "-1"

    outA0 = parse_outA(open(LEAN, encoding="utf-8").read())
    assert len(outA0) == B and all(len(r) == 3 for r in outA0), (len(outA0), [len(r) for r in outA0])
    # the port on the original file
    assert arcsOK(M, B, outA0) and symOK(M, B, outA0) and degOK(DEG, B, outA0)
    assert eccOK(M, B, D, outA0) and not eccOK(M, B, D - 1, outA0)
    assert mask_diam(M, B, outA0) == D
    assert real_diam(M, B, outA0) == D
    E0 = edges_from_outA(outA0)
    assert len(E0) == 30
    rebuilt = outA_from_E(E0)
    assert [sorted(r) for r in rebuilt] == [sorted(r) for r in outA0]
    print("self-tests ok: original passes eccOK at 13, fails at 12, real diameter 13 (%.1fs)" % (time.time() - t0))

    rng = random.Random(SEED)
    # family 1: every single voltage change on every base edge (30 edges x 169 other voltages)
    fam = []
    for i in range(len(E0)):
        for nb in range(M):
            if nb != E0[i][2]:
                E2 = [list(e) for e in E0]
                E2[i][2] = nb
                fam.append((E2, "volt edge%d->%d" % (i, nb), "volt1"))
    # family 2: random mutants (1 to 4 operations on the base edges)
    for _ in range(N_RANDOM):
        E2, dsc = random_mutant(E0, rng)
        fam.append((E2, dsc, "rand"))

    stats = {"mutants": len(fam), "invalid_arcsOK_or_symOK": 0,
             "eccOK13_pass": 0, "eccOK_pass_some_radius_le_%d" % CAP: 0,
             "counterexamples_eccOK13_and_real_gt_13": 0,
             "port_inconsistent_eccOK13_vs_mask": 0,
             "pass_by_family": {}, "pass_real_diam_hist": {},
             "fail_sample_checked": 0, "strong_real_gt_mask": 0, "strong_real_ne_mask": 0,
             "sample_fail_mask_hist": {}}
    counter, passers, fails, mask_hist_all = [], [], [], {}
    for E2, dsc, fname in fam:
        outA = outA_from_E(E2)
        if not (arcsOK(M, B, outA) and symOK(M, B, outA)):
            stats["invalid_arcsOK_or_symOK"] += 1
            continue
        e13 = eccOK(M, B, D, outA)
        md = mask_diam(M, B, outA)
        if (md is not None and md <= D) != e13:
            stats["port_inconsistent_eccOK13_vs_mask"] += 1
        if md is not None:
            stats["eccOK_pass_some_radius_le_%d" % CAP] += 1
            mask_hist_all[str(md)] = mask_hist_all.get(str(md), 0) + 1
        if e13:
            stats["eccOK13_pass"] += 1
            stats["pass_by_family"][fname] = stats["pass_by_family"].get(fname, 0) + 1
            rd = real_diam(M, B, outA)
            key = "disconnected" if rd is None else str(rd)
            stats["pass_real_diam_hist"][key] = stats["pass_real_diam_hist"].get(key, 0) + 1
            if rd is None or rd > D:
                stats["counterexamples_eccOK13_and_real_gt_13"] += 1
                counter.append({"desc": dsc, "real": rd, "eccOK13": e13})
            passers.append({"desc": dsc, "family": fname, "real": rd, "mask_diam": md})
        else:
            fails.append((E2, dsc, fname, md))
    # strong check on a sample of the mutants failing eccOK at 13 (each costs one exact BFS):
    # real diameter <= mask diameter (soundness), and equal (the masks are exact ball masks under symOK)
    srng = random.Random(SEED + 1)
    for E2, dsc, fname, md in srng.sample(fails, min(SAMPLE_FAILS, len(fails))):
        outA = outA_from_E(E2)
        rd = real_diam(M, B, outA)
        stats["fail_sample_checked"] += 1
        stats["sample_fail_mask_hist"][str(md)] = stats["sample_fail_mask_hist"].get(str(md), 0) + 1
        if md is not None and (rd is None or rd > md):
            stats["strong_real_gt_mask"] += 1
        if rd != md:
            stats["strong_real_ne_mask"] += 1
    stats["mask_diam_hist_all_valid"] = mask_hist_all
    stats["fail_mutants_at_13"] = len(fails)

    result = {"stats": stats, "counterexamples": counter[:50],
              "passers": passers[:200], "seconds": round(time.time() - t0, 1),
              "families": {"volt1": sum(1 for f in fam if f[2] == "volt1"),
                           "rand": sum(1 for f in fam if f[2] == "rand")}}
    with open(OUT, "w") as fh:
        json.dump(result, fh, indent=1)
    print(json.dumps(stats, indent=1))
    print("counterexamples:", stats["counterexamples_eccOK13_and_real_gt_13"], " eccOK13 passers:", stats["eccOK13_pass"],
          " seconds: %.1f" % (time.time() - t0))


if __name__ == "__main__":
    sys.exit(main())
