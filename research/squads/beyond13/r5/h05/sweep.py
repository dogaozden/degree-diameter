# sweep odd-order product shapes (Frobenius x Frobenius) with N in window, descending N, one haar_gen3 run each
import subprocess, sys, os, re
B = "/home/user/degree-diameter/research/frontier/beyond13"
D = "/home/user/degree-diameter/research/squads/beyond13/r5/h05"
cands = []
for line in open(sys.argv[1]):
    if not line.startswith("("): continue
    t = eval(line)
    cands.append(t)           # (N, (N1,m1,k1), (N2,m2,k2))
cands.sort(reverse=True)
STEP = int(os.environ.get('STEP', '1')); cands = cands[::STEP]
SECS = int(sys.argv[2]); MAXN = int(sys.argv[3]) if len(sys.argv) > 3 else 10**9
def root(m, k):
    for g in range(2, m):
        r = pow(g, (m - 1) // k, m)
        if r != 1: return r
seed = int(os.environ.get("SEED0", "100"))
for N, a, b in cands:
    if N > MAXN: continue
    _, m1, k1 = a; _, m2, k2 = b
    r1, r2 = root(m1, k1), root(m2, k2)
    tag = f"s_{m1}_{k1}_{m2}_{k2}_N{N}_seed{seed}"
    sol = os.path.join(D, tag + ".sol")
    log = os.path.join(D, tag + ".log")
    cmd = ["timeout", "105", "nice", "-n", "10", f"{B}/bin/haar_gen3", "5", "13", str(SECS), str(seed), "8", sol,
           "prod", "meta", str(m1), str(k1), str(r1), "meta", str(m2), str(k2), str(r2), "1"]
    env = dict(os.environ, THREADS="1")
    with open(log, "w") as f:
        subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT, env=env)
    res = [l for l in open(log) if l.startswith("RESULT")]
    print(N, m1, k1, m2, k2, seed, (res[-1].strip() if res else "NO RESULT"), flush=True)
    if res and "best=0" in res[-1] and os.path.exists(sol):
        print("SOLVED", N, sol, flush=True)
    seed += 1
