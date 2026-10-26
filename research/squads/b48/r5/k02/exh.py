import importlib.util, sys, random, time
spec = importlib.util.spec_from_file_location('en', '/home/user/degree-diameter/research/squads/b48/r5/k02/enum.py')
en = importlib.util.module_from_spec(spec); spec.loader.exec_module(en)
sys.argv = ['x', '406', '406']
want = [(29, 14, r) for r in (4, 5, 6, 9, 13, 22)]
rng = random.Random(2)
t0 = time.time()
for c in en.cands():
    N, m, k, r, I1 = c[1], c[2], c[3], c[4], c[5]
    if (m, k, r) not in want: continue
    best, nt = en.run(m, k, r, I1, rng)   # MAXT default below
    print(f"EXH N={N} m={m} k={k} r={r} tri={nt} best={best} t={time.time()-t0:.0f}", flush=True)
