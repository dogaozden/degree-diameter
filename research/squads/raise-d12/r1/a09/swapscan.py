import os, random, subprocess, sys, time
# usage: swapscan.py STATE SEED SECS OUTFILE : random single-generator swaps of the cost-1 state, evaluated by hb
state, seed, secs, out = sys.argv[1], int(sys.argv[2]), float(sys.argv[3]), sys.argv[4]
rng = random.Random(seed); M, K = 74719, 63
t0 = time.time(); n = 0; best = None
with open(out, 'a') as f:
    while time.time() - t0 < secs:
        idx = rng.randint(1, 5); a = rng.randrange(M); j = rng.randrange(K)
        env = dict(os.environ, REPL=f"{idx} {a} {j}")
        r = subprocess.run(['./hb', state], env=env, capture_output=True, text=True, timeout=20)
        cost = int(r.stdout.strip().split('\n')[-1].split('cost=')[1])
        f.write(f"{idx} {a} {j} {cost}\n"); n += 1
print("evaluated", n)
