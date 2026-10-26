import sys, random, time
sys.argv_saved = list(sys.argv)
import importlib.util
args = sys.argv[1:]
M, K, R, samples, seed = map(int, args[:5])
sys.argv = ["x", str(M), str(K), str(R)]
spec = importlib.util.spec_from_file_location("hz", "/home/user/degree-diameter/research/squads/b48/r3/d16/ana/hz.py")
hz = importlib.util.module_from_spec(spec); spec.loader.exec_module(hz)
N = hz.N; m = hz.m
rng = random.Random(seed)
z = m // 2  # central involution (m/2, 0) when m even
hist = {}; zf = 0; zcost = []; best = None; t0 = time.time()
for it in range(samples):
    S = [0] + rng.sample(range(1, N), 3)
    c, f = hz.cost(S)
    hist[c] = hist.get(c, 0) + 1
    has_z = (z in f["A"]) or (N + z in f["B"]) or (z in [x - N for x in f["B"]])  # z-element far on either side
    if has_z: zf += 1
    if best is None or c < best[0]: best = (c, S)
print("M K R", M, K, R, "samples", samples, "time %.1f" % (time.time() - t0))
print("cost hist (lowest 10):", sorted(hist.items())[:10])
print("fraction with central involution far:", round(zf / samples, 3))
print("best", best[0], [hz.lab(s) for s in best[1]])
