"""SA on the typed HHHDHHD q=5 r=3 layout (card r2c5).
usage: anneal5.py c cp steps seed T0 TAG [init.pkl]
c  = freed points on each H->H arc, cp = freed lines on the D->D arc (3->6).
Moves: swap two images in one non-friendly matching (H->H or D->D); double edge swap in the hub graph Y.
Energy = number of ordered vertex pairs at distance > 5 in the whole graph (hubs included)."""
import sys, time, math, pickle, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r2/c5')
import typed5 as T
c, cp, steps, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
T0 = float(sys.argv[5]); TAG = sys.argv[6]
init = sys.argv[7] if len(sys.argv) > 7 else None
rng = np.random.default_rng(seed)

def fresh():
    s = T.State()
    for t in T.ARCS:
        f = T.friendly_R(t)
        if f is not None:
            s.R[t] = f; s.M[t] = np.arange(T.N)
        else:
            k = c if T.TYPES[t[0]] == 'H' else cp
            s.R[t] = sorted(rng.choice(T.N, k, replace=False).tolist())
            s.M[t] = rng.permutation(T.N)
    T.set_hubs(s, rng)
    s.Y = random_Y(s)
    return s

def random_Y(s):
    E = T.DELTA * min(s.KB, s.KA)
    stB = [h for h in range(s.KB) for _ in range(E // s.KB + (1 if h < E % s.KB else 0))]
    stA = [g for g in range(s.KA) for _ in range(E // s.KA + (1 if g < E % s.KA else 0))]
    while True:
        rng.shuffle(stA); Y = set(zip(stB, stA))
        if len(Y) == E: return list(Y)

if init:
    st = pickle.load(open(init, 'rb'))
    s = st['state']
else:
    s = fresh()
cur = T.bad_count(s); best = cur; bests = s.copy()
print('start', 'KB', s.KB, 'KA', s.KA, 'n', T.NV + s.KB + s.KA, 'bad', cur, flush=True)
t0 = time.time()
for it in range(steps):
    Temp = T0 * (1 - it / steps) + 0.02
    if rng.random() < 0.85:
        t = T.HUB_ARCS[rng.integers(len(T.HUB_ARCS))]
        x, z = rng.choice(T.N, 2, replace=False)
        M = s.M[t]; M[x], M[z] = M[z], M[x]
        new = T.bad_count(s); d = new - cur
        if d <= 0 or rng.random() < math.exp(-d / Temp):
            cur = new
        else:
            M[x], M[z] = M[z], M[x]
    elif rng.random() < 0.4:
        # slot re-assignment: swap two hubs' slots in one level (B-hubs: sigma, A-hubs: tau)
        j = int(rng.integers(T.L))
        if rng.random() < 0.5:
            perm = s.sigma[j]; a, b = rng.choice(len(perm), 2, replace=False)
            perm[a], perm[b] = perm[b], perm[a]
            new = T.bad_count(s); d = new - cur
            if d <= 0 or rng.random() < math.exp(-d / Temp): cur = new
            else: perm[a], perm[b] = perm[b], perm[a]
        else:
            perm = s.tau[j]; a, b = rng.choice(len(perm), 2, replace=False)
            perm[a], perm[b] = perm[b], perm[a]
            new = T.bad_count(s); d = new - cur
            if d <= 0 or rng.random() < math.exp(-d / Temp): cur = new
            else: perm[a], perm[b] = perm[b], perm[a]
    else:
        Y = s.Y
        i, j = rng.integers(len(Y), size=2)
        (h1, g1), (h2, g2) = Y[i], Y[j]
        if h1 != h2 and g1 != g2 and (h1, g2) not in Y and (h2, g1) not in Y:
            old = (Y[i], Y[j]); Y[i] = (h1, g2); Y[j] = (h2, g1)
            new = T.bad_count(s); d = new - cur
            if d <= 0 or rng.random() < math.exp(-d / Temp):
                cur = new
            else:
                Y[i], Y[j] = old
    if cur < best:
        best = cur; bests = s.copy()
        if best == 0: break
    if it % 300 == 0:
        print('it', it, 'cur', cur, 'best', best, 'T %.2f' % Temp, 'el %.0f' % (time.time() - t0), flush=True)
print('FINAL', TAG, 'c', c, 'cp', cp, 'seed', seed, 'best', best, 'n', T.NV + bests.KB + bests.KA, flush=True)
pickle.dump({'state': bests, 'best': best, 'c': c, 'cp': cp}, open('/home/user/degree-diameter/research/squads/gqd5-r2/c5/state_%s.pkl' % TAG, 'wb'))
if best == 0:
    p = '/home/user/degree-diameter/research/squads/gqd5-r2/c5/best_%s.edges' % TAG
    T.write_edge_file(bests, p)
    import subprocess
    print(subprocess.run(['timeout', '900', '/home/user/degree-diameter/research/theorems/d5gq/apsp', p, '9', '5'],
                         capture_output=True, text=True).stdout.strip(), flush=True)
