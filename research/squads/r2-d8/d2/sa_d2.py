"""Simulated annealing of Z_5 voltages on a card-d2 base (variant A = card example, B = one copy per in-arc + matching).
Cost = unreached_pairs from liftdiam at D=8 over sampled base sources (src_step), full check at the end.
Usage: python3 sa_d2.py A|B seed seconds src_step"""
import sys, random, subprocess, math, time, re
sys.path.insert(0, '/home/user/degree-diameter/research/squads/r2-d8/d2')
import build_d2 as BA
import build_d2b as BB
LD = '/home/user/degree-diameter/research/theorems/d8/liftdiam'
variant = sys.argv[1]; seed = int(sys.argv[2]); secs = float(sys.argv[3]); step = int(sys.argv[4])
if variant == 'A':
    NW, E, _, _ = BA.build_base(1)
else:
    NW, E, _, _ = BB.build_B(1, True)
rng = random.Random(seed)
volts = [rng.randrange(5) for _ in E]
tmp = f'/home/user/degree-diameter/research/squads/r2-d8/d2/tmp_{variant}_{seed}.txt'
def cost(vs, st):
    BA.write_lift_file(tmp, NW, E, vs)
    out = subprocess.run(['timeout', '900', 'nice', '-n', '10', LD, tmp, '8', '1', str(st)], capture_output=True, text=True).stdout
    m = re.search(r'unreached_pairs (\d+)', out)
    return int(m.group(1))
cur = cost(volts, step); best = cur; bestv = volts[:]
print('init', cur, flush=True)
t0 = time.time(); it = 0; T0 = 0.02 * cur if cur > 0 else 1.0
while time.time() - t0 < secs:
    it += 1
    T = T0 * (1 - (time.time() - t0) / secs) + 1e-9
    i = rng.randrange(len(E)); old = volts[i]
    volts[i] = (old + rng.randrange(1, 5)) % 5
    c = cost(volts, step)
    if c <= cur or rng.random() < math.exp(-(c - cur) / T):
        cur = c
        if c < best: best = c; bestv = volts[:]
    else:
        volts[i] = old
    if it % 300 == 0: print('it', it, 'cur', cur, 'best', best, 'T', round(T, 1), flush=True)
full = None
BA.write_lift_file(f'/home/user/degree-diameter/research/squads/r2-d8/d2/best_{variant}_{seed}.txt', NW, E, bestv)
full = cost(bestv, 1)
print('done iters', it, 'best sampled', best, 'full check', full, flush=True)
