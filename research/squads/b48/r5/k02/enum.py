# k02: bi-Cayley lifts of the base "2 4 / 0 1 / 0 1 / 0 0 s / 1 1 s" (two parallel edges + one semi-edge per vertex)
# Gauge: tree edge (edge 0) voltage e. Free: g2 (edge 1, chi even), s0, s1 (edges 2,3: involutions with chi odd).
# Parity chi(a,j) = j mod 2 with k even; involutions with chi odd exist only at j = k/2 (need k = 2 mod 4).
import subprocess, sys, time, random, math
T = "/home/user/degree-diameter/research/squads/b48/tools"
D = "/home/user/degree-diameter/research/squads/b48/r5/k02"
LO, HI = int(sys.argv[1]), int(sys.argv[2])
MAXT = int(sys.argv[3]) if len(sys.argv) > 3 else 120000
BUDGET = float(sys.argv[4]) if len(sys.argv) > 4 else 60.0
def cands():
    out = []
    for N in range(LO, HI + 1):
        for k in range(int(__import__("os").environ.get("MINK", "2")), N + 1, 4):   # k = 2 mod 4
            if N % k: continue
            m = N // k
            for r in range(1, m + 1):
                if m > 1 and math.gcd(r, m) != 1: continue
                if pow(r, k, m) != 1 % m: continue
                h = k // 2
                rh = pow(r, h, m)
                I1 = [a + m * h for a in range(m) if (a * (1 + rh)) % m == 0]
                if not I1: continue
                out.append((len(I1), N, m, k, r, I1))
    return out
def run(m, k, r, I1, rng):
    N = m * k
    chi0 = [a + m * j for j in range(0, k, 2) for a in range(m) if a + m * j != 0]
    tri = [(g2, s0, s1) for g2 in chi0 for s0 in I1 for s1 in I1]
    if len(tri) > MAXT:
        rng.shuffle(tri); tri = tri[:MAXT]
    lines = "".join(f"0 {g2 + 0} {s0} {s1}\n".replace("0 ", "0 ", 1) for g2, s0, s1 in tri)
    # index of tree edge is 0 (identity), so the line is "0 g2 s0 s1"
    p = subprocess.run([f"{T}/lift", f"{D}/base_k02.txt", f"meta:{m}:{k}:{r}", "3", "10", "eval"],
                       input=lines, capture_output=True, text=True, timeout=300,
                       env={"THREADS": "1", "QUIET": "1", "PATH": "/usr/bin:/bin"})
    vals = p.stdout.split("\n")
    best = None
    for (g2, s0, s1), v in zip(tri, vals):
        if v == "invalid" or v == "": continue
        c = int(v)
        if best is None or c < best[0]: best = (c, g2, s0, s1)
    return best, len(tri)
if __name__ == "__main__":
    t0 = time.time()
    rng = random.Random(1)
    cs = sorted(cands(), key=lambda x: (-x[0], x[3]))
    print("candidates", len(cs), flush=True)
    res = []
    for ni, m, k, r, I1 in [(c[0], c[2], c[3], c[4], c[5]) for c in cs]:
        pass
    for c in cs:
        if time.time() - t0 > BUDGET: break
        I, N, m, k, r, I1 = c[0], c[1], c[2], c[3], c[4], c[5]
        best, nt = run(m, k, r, I1, rng)
        res.append((best[0] if best else None, N, m, k, r, best, nt))
        print(f"N={N} m={m} k={k} r={r} |I1|={len(I1)} tri={nt} best={best}", flush=True)
    res = [x for x in res if x[0] is not None]
    res.sort(key=lambda x: x[0])
    print("TOP", res[:10], flush=True)
