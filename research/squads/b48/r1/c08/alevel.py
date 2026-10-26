# Level 2: fix the Z_k-parts J = (0, J1, J2, J3) of S and enumerate the Z_m-parts exhaustively with `lift eval`.
# Automorphisms (a,j) -> (u*a, j), u a unit of Z_m, fix e and act on the a-parts; so a1 only needs
# one representative per gcd class (a1 in {0} + divisors of m), a2 and a3 run over all of Z_m.
import sys, subprocess, math, os, time
T = "/home/user/degree-diameter/research/squads/b48/tools"
def run(m, k, r, J, reps_limit=None, base=f"{T}/bases/dipole4.txt"):
    grp = f"meta:{m}:{k}:{r}"
    divs = [d for d in range(1, m) if m % d == 0]
    a1s = [0] + divs  # gcd classes of a1 (0 is its own class)
    lines = []
    for a1 in a1s:
        for a2 in range(m):
            for a3 in range(m):
                a = [0, a1, a2, a3]
                lines.append(" ".join(str(a[i] + m * J[i]) for i in range(4)))
    inp = "\n".join(lines) + "\n"
    env = dict(os.environ, THREADS="1")
    p = subprocess.run(["nice", "-n", "10", "timeout", "120", f"{T}/lift", base, grp, "4", "8", "eval"],
                       input=inp, capture_output=True, text=True, env=env)
    vals = p.stdout.split()
    best = None
    for i, v in enumerate(vals):
        if v == "invalid": continue
        c = int(v)
        if best is None or c < best[0]:
            best = (c, lines[i])
    hist = {}
    for v in vals:
        if v != "invalid": hist[int(v)] = hist.get(int(v), 0) + 1
    return best, len(vals), min(hist) if hist else None, sum(1 for v in vals if v == "invalid"), p.stderr[-300:]
if __name__ == "__main__":
    m, k, r = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    J = [int(x) for x in sys.argv[4].split(",")]
    t0 = time.time()
    best, nev, mn, ninv, err = run(m, k, r, J)
    print(f"m={m} k={k} r={r} J={J} evals={nev} invalid={ninv} best={best} time={time.time()-t0:.1f}", flush=True)
    if err.strip(): print("stderr:", err)
