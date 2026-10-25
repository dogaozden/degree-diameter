import sys, time, random
sys.path.insert(0, '/home/user/degree-diameter/research/squads/r1-d8/c2')
import holo, gh
from holo import Q, SCR
H = gh.load(5)
N = H.N
# calibration: random flag voltages (no structure), hops random, labels random
for k in [int(x) for x in sys.argv[1].split(',')]:
    res = []
    for s in [0, 1]:
        rng = random.Random(100 + s)
        lam = holo.lam_table(H, holo.frames(H, 'first'))
        Fv = [rng.randrange(k) for _ in range(Q + 1)]  # lam-dependent constant only -> not fully random
        # fully random per flag:
        edges = []
        for (p, L) in gh.flags(H):
            edges.append((p, L, 0, rng.randrange(k)))
        s1 = list(range(N)); rng.shuffle(s1); s2 = list(range(N)); rng.shuffle(s2)
        for p in range(N):
            edges.append((p, N + s1[p], 1, rng.randrange(k)))
            edges.append((p, N + s2[p], 2, rng.randrange(k)))
        path = f'{SCR}/calib_k{k}_s{s}.txt'
        gh.write_base(path, 2 * N, Q, k, edges)
        import subprocess
        out = subprocess.run(['timeout', '900', 'nice', '-n', '10', holo.LD, path, '8', '1', '1'], capture_output=True, text=True).stdout
        res.append(int(out.split('unreached_pairs')[1].split()[0]))
    print('random flags k', k, 'M', 5 * k, 'unreached', res, flush=True)
