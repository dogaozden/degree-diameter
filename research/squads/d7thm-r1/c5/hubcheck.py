#!/usr/bin/env python3
"""Card c5: hub-graph constructions (A) blow-up, (B) sum of parts, (C) plane with pendant trees.
Distances are checked by bfs.c (all-pairs BFS). Run from the c5 folder: python3 hubcheck.py [seed]."""
import itertools, os, random, struct, subprocess, sys
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
BFS = os.path.join(HERE, "bfs")
SEED = int(sys.argv[1]) if len(sys.argv) > 1 else 5
rng = random.Random(SEED)


class G:
    """Graph with colour classes 0 (A) and 1 (B). Vertices 0..n-1, edges as (u, v) pairs."""
    def __init__(self, n, col, edges, tag=""):
        self.n, self.col, self.edges, self.tag = n, list(col), list(edges), tag
        self.nA = sum(1 for c in self.col if c == 0)
        self.nB = n - self.nA

    def maxdeg(self):
        d = [0] * self.n
        for u, v in self.edges:
            d[u] += 1; d[v] += 1
        return max(d) if d else 0


def bfs_check(g, sameT=6, diffT=5):
    lines = [f"{g.n} {len(g.edges)}", " ".join(map(str, g.col))] + [f"{u} {v}" for u, v in g.edges]
    out = subprocess.run([BFS, str(sameT), str(diffT)], input="\n".join(lines) + "\n",
                         capture_output=True, text=True, check=True).stdout.split()
    keys = ["n", "maxdeg", "maxsame", "sameviol", "maxdiff", "diffviol", "connected", "ex_u", "ex_v", "ex_d"]
    return dict(zip(keys, map(int, out)))


# ---------- finite fields and PG(2,s) ----------
def field(q):
    """ADD and MUL tables for GF(q), q in {2,3,4,5}; GF(4) elements a0 + 2 a1 with x^2+x+1 (as in hexgen2)."""
    if q == 4:
        mul = lambda a, b: _gf4mul(a, b)
        add = lambda a, b: a ^ b
        return [[add(a, b) for b in range(4)] for a in range(4)], [[mul(a, b) for b in range(4)] for a in range(4)]
    ADD = [[(a + b) % q for b in range(q)] for a in range(q)]
    MUL = [[(a * b) % q for b in range(q)] for a in range(q)]
    return ADD, MUL


def _gf4mul(a, b):
    r = 0
    for i in range(2):
        if (b >> i) & 1:
            r ^= a << i
    if r & 4:
        r ^= 7  # x^2 = x + 1
    return r


def pg2(s):
    """Incidence graph of PG(2,s): points 0..n-1 (colour A), lines n..2n-1 (colour B)."""
    ADD, MUL = field(s)
    pts = []
    for v in itertools.product(range(s), repeat=3):
        if any(v):
            f = next(x for x in v if x)
            inv = next(y for y in range(1, s) if MUL[f][y] == 1)
            w = tuple(MUL[inv][x] for x in v)
            if w == v and w not in pts:
                pts.append(w)
    n = len(pts)
    assert n == s * s + s + 1, (s, n)
    edges = []
    for li, L in enumerate(pts):
        for pi, P in enumerate(pts):
            acc = 0
            for k in range(3):
                acc = ADD[acc][MUL[P[k]][L[k]]]
            if acc == 0:
                edges.append((pi, n + li))
    return G(2 * n, [0] * n + [1] * n, edges, tag=f"PG(2,{s})"), n


# ---------- H(q) from hexgen2 output ----------
def load_hex(q):
    path = os.path.join(HERE, "hex", f"hex_q{q}.bin")
    with open(path, "rb") as f:
        qq, N, L = struct.unpack("<iii", f.read(12))
        assert qq == q
        ids = np.frombuffer(f.read(4 * L * (q + 1)), dtype="<i4").reshape(L, q + 1)
    edges = [(int(p), N + l) for l in range(L) for p in ids[l]]
    return G(N + L, [0] * N + [1] * L, edges, tag=f"H({q})")


# ---------- (A) blow-up ----------
def blowup(g, c, r):
    t = [r.randint(1, c) for _ in range(g.n)]
    off = [0] * (g.n + 1)
    for v in range(g.n):
        off[v + 1] = off[v] + t[v]
    col = []
    for v in range(g.n):
        col += [g.col[v]] * t[v]
    edges = []
    for u, v in g.edges:
        for a in range(t[u]):
            for b in range(t[v]):
                edges.append((off[u] + a, off[v] + b))
    # predicted maximum degree: max over v of sum of t_w over neighbours w of v
    pred = [0] * g.n
    for u, v in g.edges:
        pred[u] += t[v]; pred[v] += t[u]
    return G(off[-1], col, edges, tag=f"blowup({g.tag},c={c})"), max(pred)


# ---------- (C) plane with pendant trees ----------
def pendant_plane(s, t, u, cP, cL, gP, gL, r):
    core, n = pg2(s)
    col = list(core.col)
    edges = list(core.edges)
    nv = 2 * n

    def new(colour):
        nonlocal nv
        col.append(colour); nv += 1
        return nv - 1

    d1P, d1L = [], []
    for p in r.sample([p for p in range(n) for _ in range(t)], cP):
        x = new(1); edges.append((p, x)); d1P.append(x)
    for L in r.sample([n + l for l in range(n) for _ in range(t)], cL):
        x = new(0); edges.append((L, x)); d1L.append(x)
    for y in r.sample([y for y in d1P for _ in range(u)], gP):
        x = new(0); edges.append((y, x))
    for z in r.sample([z for z in d1L for _ in range(u)], gL):
        x = new(1); edges.append((z, x))
    g = G(nv, col, edges, tag=f"C(s={s},t={t},u={u},cP={cP},cL={cL},gP={gP},gL={gL})")
    assert g.nA == n + cL + gP and g.nB == n + cP + gL
    return g, s + 1 + t, u + 1


# ---------- (B) sum ----------
def sides(g):
    return g.nA, g.nB


def valid_orders(parts, must_last=None, must_not_last=None):
    r = len(parts)
    out = []
    for perm in itertools.permutations(range(r)):
        if must_last is not None and perm[-1] != must_last:
            continue
        if must_not_last is not None and perm[-1] == must_not_last:
            continue
        ok = True
        for i in range(r):
            for j in range(i + 1, r):
                pi, pj = parts[perm[i]], parts[perm[j]]
                if not (pj.nA <= pi.nB and pj.nB <= pi.nA):
                    ok = False
                    break
            if not ok:
                break
        if ok:
            out.append(perm)
    return out


def build_sum(ordered, r):
    edges, col, offs, off = [], [], [], 0
    for g in ordered:
        offs.append(off)
        edges += [(u + off, v + off) for u, v in g.edges]
        col += g.col
        off += g.n
    As = [[offs[i] + v for v in range(g.n) if g.col[v] == 0] for i, g in enumerate(ordered)]
    Bs = [[offs[i] + v for v in range(g.n) if g.col[v] == 1] for i, g in enumerate(ordered)]
    for i in range(len(ordered)):
        for j in range(i + 1, len(ordered)):
            # injective map A_j -> B_i and B_j -> A_i, realised as edges
            for a, b in zip(As[j], r.sample(Bs[i], len(As[j]))):
                edges.append((a, b))
            for b, a in zip(Bs[j], r.sample(As[i], len(Bs[j]))):
                edges.append((b, a))
    return G(off, col, edges, tag="sum")


def random_blowup_part(bases, r):
    s = r.choice([2, 3]); c = r.choice([2, 3])
    g, pred = blowup(bases[s], c, r)
    g.s, g.c, g.pred = s, c, pred
    g.base_maxdeg = max(p for p in [pred])  # placeholder, real own-degree is g.maxdeg()
    return g


def random_C_part(r, mode):
    s = r.choice([2, 3, 4, 5])
    n = s * s + s + 1
    t, u = r.randint(1, 3), r.randint(1, 3)
    if mode == "uniform":
        cP, cL = r.randint(0, t * n), r.randint(0, t * n)
        gP, gL = r.randint(0, u * cP), r.randint(0, u * cL)
    else:  # extreme sides: each count is 0 or its maximum, or random
        cP = r.choice([0, t * n, r.randint(0, t * n)])
        cL = r.choice([0, t * n, r.randint(0, t * n)])
        gP = r.choice([0, u * cP, r.randint(0, u * cP)])
        gL = r.choice([0, u * cL, r.randint(0, u * cL)])
    g, sb, ub = pendant_plane(s, t, u, cP, cL, gP, gL, r)
    g.bound = max(sb, ub)
    return g


def main():
    bases = {2: load_hex(2), 3: load_hex(3)}
    log = []

    def P(*a):
        s = " ".join(str(x) for x in a)
        print(s); log.append(s)

    # sanity on base graphs
    for name, g in [("H(2)", bases[2]), ("H(3)", bases[3]), ("PG(2,2)", pg2(2)[0]),
                    ("PG(2,3)", pg2(3)[0]), ("PG(2,4)", pg2(4)[0]), ("PG(2,5)", pg2(5)[0])]:
        res = bfs_check(g, 6, 5) if name.startswith("H") else bfs_check(g, 2, 3)
        P(f"base {name}: n={res['n']} maxdeg={res['maxdeg']} maxsame={res['maxsame']} maxdiff={res['maxdiff']} connected={res['connected']}")

    # ---------- (A) ----------
    A_pass, A_total, A_pred_ok = 0, 0, 0
    for s in (2, 3):
        for c in (2, 3):
            for k in range(5):
                g, pred = blowup(bases[s], c, rng)
                res = bfs_check(g, 6, 5)
                ok = res["sameviol"] == 0 and res["diffviol"] == 0 and res["maxdeg"] <= c * (s + 1) and res["connected"] == 1
                pred_ok = (res["maxdeg"] == pred)
                A_total += 1; A_pass += ok; A_pred_ok += pred_ok
                P(f"A s={s} c={c} k={k}: n={res['n']} maxsame={res['maxsame']} maxdiff={res['maxdiff']} "
                  f"sameviol={res['sameviol']} diffviol={res['diffviol']} maxdeg={res['maxdeg']} "
                  f"(pred {pred}, bound {c*(s+1)}) {'PASS' if ok else 'FAIL'}")
    P(f"(A) pass {A_pass}/{A_total}; degree formula exact in {A_pred_ok}/{A_total}")

    # ---------- (B) ----------
    B_pass, B_total, B_rej = 0, 0, 0
    for inst in range(20):
        while True:
            r_ = rng.randint(2, 5)
            parts = [random_blowup_part(bases, rng) for _ in range(r_ - 1)]
            last_C = rng.random() < 0.5
            last = random_C_part(rng, rng.choice(["uniform", "extreme"])) if last_C else random_blowup_part(bases, rng)
            parts.append(last)
            if last_C:
                orders = valid_orders(parts, must_last=r_ - 1)
            else:
                orders = valid_orders(parts)
            if orders:
                break
            B_rej += 1
        perm = rng.choice(orders)
        ordered = [parts[k] for k in perm]
        S = build_sum(ordered, rng)
        res = bfs_check(S, 6, 5)
        own = max(g.maxdeg() for g in ordered)
        degbound = own + r_ - 1
        ok = res["sameviol"] == 0 and res["connected"] == 1 and res["maxdeg"] <= degbound
        B_total += 1; B_pass += ok
        names = ",".join(f"{g.tag}[A{g.nA},B{g.nB}]" for g in ordered)
        P(f"B inst={inst} r={r_}: n={res['n']} maxsame={res['maxsame']} sameviol={res['sameviol']} "
          f"maxdeg={res['maxdeg']} bound={degbound} {'PASS' if ok else 'FAIL'} :: {names}")
    P(f"(B) pass {B_pass}/{B_total}; resampled {B_rej} times for the side-size ordering constraint")

    # ---------- (B) negative control: (C) first, later parts map into it ----------
    N_viol, N_total, N_rej = 0, 0, 0
    for inst in range(20):
        while True:
            r_ = rng.randint(2, 3)
            Cp = random_C_part(rng, rng.choice(["uniform", "extreme"]))
            parts = [Cp] + [random_blowup_part(bases, rng) for _ in range(r_ - 1)]
            orders = valid_orders(parts, must_not_last=0)
            orders = [o for o in orders if o[0] == 0]
            if orders:
                break
            N_rej += 1
        perm = rng.choice(orders)
        ordered = [parts[k] for k in perm]
        S = build_sum(ordered, rng)
        res = bfs_check(S, 6, 5)
        viol = res["sameviol"] > 0
        N_total += 1; N_viol += viol
        P(f"NEG inst={inst} r={r_}: maxsame={res['maxsame']} sameviol={res['sameviol']} "
          f"example pair ({res['ex_u']},{res['ex_v']}) dist {res['ex_d']} :: {Cp.tag}")
    P(f"(B-neg) same-colour violation found in {N_viol}/{N_total}; resampled {N_rej} times")

    # ---------- (C) ----------
    C_pass, C_total = 0, 0
    for inst in range(30):
        mode = "uniform" if inst < 15 else "extreme"
        g = random_C_part(rng, mode)
        res = bfs_check(g, 6, 5)
        ok = res["sameviol"] == 0 and res["connected"] == 1 and res["maxdeg"] <= g.bound
        C_total += 1; C_pass += ok
        P(f"C inst={inst} {mode}: n={res['n']} nA={g.nA} nB={g.nB} maxsame={res['maxsame']} "
          f"sameviol={res['sameviol']} maxdeg={res['maxdeg']} bound={g.bound} {'PASS' if ok else 'FAIL'} :: {g.tag}")
    P(f"(C) pass {C_pass}/{C_total}")

    P(f"SUMMARY seed={SEED}: A {A_pass}/{A_total}, B {B_pass}/{B_total}, C {C_pass}/{C_total}, "
      f"score(A+B+C)={A_pass + B_pass + C_pass}/{A_total + B_total + C_total}; negative control violations {N_viol}/{N_total}")
    with open(os.path.join(HERE, f"results_seed{SEED}.txt"), "w") as f:
        f.write("\n".join(log) + "\n")


if __name__ == "__main__":
    main()
