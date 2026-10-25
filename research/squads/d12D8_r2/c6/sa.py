"""Simulated annealing over affine labels of a simple base; energy = total uncovered (affcheck, STEP=1 XSTEP=1).
usage: sa.py BASE ITERS T0 T1 seed OUT   (OUT receives the best base file; prints progress)"""
import sys, math, random, subprocess, re, shutil
import numpy as np
AFF = '/home/user/degree-diameter/research/d12D8/tools/affcheck'
base, iters, T0, T1, seed, out = sys.argv[1], int(sys.argv[2]), float(sys.argv[3]), float(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
rng = random.Random(seed)
with open(base) as f:
    NP, NL, m, _ = f.readline().split(); NP, NL, m = int(NP), int(NL), int(m)
    E = [list(map(int, ln.split())) for ln in f if ln.strip()]
units = [a for a in range(1, m) if np.gcd(a, m) == 1]
tmp = out + '.tmp'
def write(EE, fn):
    with open(fn, 'w') as g:
        g.write(f"{NP} {NL} {m} aff\n")
        for p, l, a, b in EE: g.write(f"{p} {l} {a} {b}\n")
def energy(EE):
    write(EE, tmp)
    r = subprocess.run([AFF, tmp, '1', '1'], capture_output=True, text=True, env={'OMP_NUM_THREADS': '1', 'PATH': '/usr/bin:/bin'})
    mm = re.search(r'total uncovered (\d+)', r.stdout)
    return int(mm.group(1)) if mm else 10**9
cur = energy(E); best = cur; bestE = [list(e) for e in E]
print('start', cur, flush=True)
for it in range(iters):
    T = T0 * (T1 / T0) ** (it / max(1, iters - 1))
    i = rng.randrange(len(E)); old = E[i][:]
    r = rng.random()
    if r < 0.4: E[i][2] = rng.choice(units)
    elif r < 0.8: E[i][3] = rng.randrange(m)
    else: E[i][2] = rng.choice(units); E[i][3] = rng.randrange(m)
    if E[i] == old: continue
    new = energy(E)
    d = new - cur
    if d <= 0 or rng.random() < math.exp(-d / T):
        cur = new
        if cur < best:
            best = cur; bestE = [list(e) for e in E]
            print('it', it, 'best', best, 'T', round(T, 3), flush=True)
            write(bestE, out)
            if best == 0: break
    else:
        E[i] = old
    if it % 200 == 0: print('it', it, 'cur', cur, 'best', best, flush=True)
write(bestE, out)
print('final best', best, flush=True)
