#!/usr/bin/env python3
"""card c4: exhaustive Haar-graph search (S = {e, a, b}) over many groups of order 400.

Group tables come from research/d5/groups.py (imported, nothing written there) plus extra semidirect
products Z_p^2 x| Z_K (A in GL(2,p), A^K = I) built here. Each table goes to tables/LABEL.txt; haar_c4
searches all pairs; cost-0 graphs go to edges/LABEL.txt. Results: results.tsv.
"""
import sys, os, itertools, math, subprocess, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, "/home/user/degree-diameter/research/d5")
import groups as G  # noqa: E402

TAB = os.path.join(HERE, "tables"); EDG = os.path.join(HERE, "edges")
os.makedirs(TAB, exist_ok=True); os.makedirs(EDG, exist_ok=True)
C = os.path.join(HERE, "haar_c4")
RES = os.path.join(HERE, "results.tsv")
I2 = (1, 0, 0, 1)


def mm2(X, Y, p):
    a, b, c, d = X; e, f, g, h = Y
    return ((a * e + b * g) % p, (a * f + b * h) % p, (c * e + d * g) % p, (c * f + d * h) % p)


def mpow(A, k, p):
    R = I2
    for _ in range(k):
        R = mm2(R, A, p)
    return R


def z2sd(p, K, A):
    """Z_p^2 x| Z_K, generator acting by A (A^K = I). Element (x, y, j); (x,y,j)(u,v,l) = ((x,y)+A^j(u,v), j+l)."""
    if mpow(A, K, p) != I2:
        raise ValueError("A^K != I")
    Ap = [I2]
    for _ in range(K - 1):
        Ap.append(mm2(Ap[-1], A, p))

    def mul(g, h):
        (x, y, j), (u, v, l) = g, h
        M = Ap[j]
        return ((x + M[0] * u + M[1] * v) % p, (y + M[2] * u + M[3] * v) % p, (j + l) % K)

    els = [(x, y, j) for x in range(p) for y in range(p) for j in range(K)]
    return G.from_mul(els, mul, (0, 0, 0))


def gl2_classes(p, K):
    """One matrix per conjugacy class of GL(2,p) (non-identity) with A^K = I. Key (trace, det, scalar)."""
    reps = {}
    for A in itertools.product(range(p), repeat=4):
        a, b, c, d = A
        if (a * d - b * c) % p == 0 or A == I2:
            continue
        if mpow(A, K, p) != I2:
            continue
        key = ((a + d) % p, (a * d - b * c) % p, b == 0 and c == 0 and a == d)
        reps.setdefault(key, A)
    return list(reps.values())


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def group_specs():
    specs = []
    # 1. Z_p^2 x| Z_16 (p=5), Z_2^2 x| Z_100, Z_p^2 x| Z_8 x Z_2, Z_p^2 x| Z_4 x (cyclic/Klein)
    for A in gl2_classes(5, 16):
        specs.append((f"z2sd_5_16_{A[0]}{A[1]}{A[2]}{A[3]}", lambda A=A: z2sd(5, 16, A)))
    for A in gl2_classes(2, 100):
        specs.append((f"z2sd_2_100_{A[0]}{A[1]}{A[2]}{A[3]}", lambda A=A: z2sd(2, 100, A)))
    for A in gl2_classes(5, 8):
        specs.append((f"z2sd_5_8_{A[0]}{A[1]}{A[2]}{A[3]}__x__cyc_2",
                      lambda A=A: G.product(z2sd(5, 8, A), G.cyclic(2))))
    for A in gl2_classes(5, 4):
        specs.append((f"z2sd_5_4_{A[0]}{A[1]}{A[2]}{A[3]}__x__cyc_4",
                      lambda A=A: G.product(z2sd(5, 4, A), G.cyclic(4))))
        specs.append((f"z2sd_5_4_{A[0]}{A[1]}{A[2]}{A[3]}__x__cyc_2_2",
                      lambda A=A: G.product(z2sd(5, 4, A), G.product(G.cyclic(2), G.cyclic(2)))))
    # 2. metacyclic Z_M x| Z_K, M*K = 400, nontrivial action
    for M in divisors(400):
        K = 400 // M
        if M < 3 or K < 2:
            continue
        for lam in range(2, M):
            if math.gcd(lam, M) != 1 or pow(lam, K, M) != 1 % M:
                continue
            specs.append((f"meta_{M}_{K}_{lam}", lambda M=M, K=K, lam=lam: G.meta(M, K, lam)))
    # 3. products with cyclic / small groups of order 8 and 2
    specs.append(("meta_25_4_7__x__cyc_4", lambda: G.product(G.meta(25, 4, 7), G.cyclic(4))))
    for A in gl2_classes(5, 2):
        for name, H in [("cyc_8", lambda: G.cyclic(8)), ("meta_8_2_3", lambda: G.meta(8, 2, 3)),
                        ("meta_4_2_3", lambda: G.meta(4, 2, 3))]:
            specs.append((f"z2sd_5_2_{A[0]}{A[1]}{A[2]}{A[3]}__x__{name}",
                          lambda A=A, H=H: G.product(z2sd(5, 2, A), H())))
    return specs


def run(label, build, log):
    t0 = time.time()
    T = build()
    N = len(T)
    if N != 400:
        raise RuntimeError(f"{label}: order {N}")
    tpath = os.path.join(TAB, label + ".txt")
    G.write_table(tpath, T)
    epath = os.path.join(EDG, label + ".txt")
    try:
        os.remove(epath)
    except OSError:
        pass
    out = subprocess.run(["timeout", "600", "nice", "-n", "10", C, tpath, epath],
                         capture_output=True, text=True).stdout.strip()
    line = out.splitlines()[-1] if out else "NO_OUTPUT"
    best = None
    for tok in line.split():
        if tok.startswith("best="):
            best = int(tok[5:])
    zero = os.path.exists(epath)
    row = f"{label}\t{line}\t{time.time() - t0:.1f}s"
    print(row, flush=True)
    with open(RES, "a") as f:
        f.write(row + "\n")
    return best, zero


if __name__ == "__main__":
    specs = group_specs()
    print(f"{len(specs)} group specs", flush=True)
    done = 0
    results = []
    for label, build in specs:
        try:
            best, zero = run(label, build, None)
            results.append((best, label, zero))
            if zero:
                print("FOUND cost 0:", label, flush=True)
        except Exception as e:  # keep going on construction errors
            with open(RES, "a") as f:
                f.write(f"{label}\tERROR {e}\n")
            print("ERROR", label, e, flush=True)
        done += 1
    results.sort()
    print("TOP:", results[:5], flush=True)
