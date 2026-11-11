# one haar_gen3 run on prod meta(m1,k1) x meta(m2,k2) for d=5 D=13; prints RESULT line and VALID flag
import subprocess, sys, os
B = "/home/user/degree-diameter/research/frontier/beyond13"
D = "/home/user/degree-diameter/research/squads/beyond13/r6/i06"
m1, k1, m2, k2, seed, secs = map(int, sys.argv[1:7])
def root(m, k):
    for g in range(2, m):
        r = pow(g, (m - 1) // k, m)
        if r != 1 and pow(r, k, m) == 1: return r
r1, r2 = root(m1, k1), root(m2, k2)
N = m1 * k1 * m2 * k2
tag = f"p_{m1}_{k1}_{m2}_{k2}_N{N}_s{seed}"
sol = os.path.join(D, tag + ".sol")
cmd = ["timeout", "105", "nice", "-n", "10", f"{B}/bin/haar_gen3", "5", "13", str(secs), str(seed), "8", sol,
       "prod", "meta", str(m1), str(k1), str(r1), "meta", str(m2), str(k2), str(r2), "1"]
env = dict(os.environ, THREADS="1")
with open(os.path.join(D, tag + ".log"), "w") as f:
    subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT, env=env)
res = [l.strip() for l in open(os.path.join(D, tag + ".log")) if l.startswith("RESULT")]
print(N, m1, k1, m2, k2, seed, res[-1] if res else "NO RESULT", flush=True)
