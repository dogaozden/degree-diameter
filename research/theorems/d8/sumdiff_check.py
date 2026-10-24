"""Check the n+2 covers of sumdiff.py on H(q) with random matchings: diameter <= 8 expected."""
import random, subprocess, sys
import gh
SCR = '/tmp/claude-0/-home-user-degree-diameter/0ad899b8-ae47-58b5-b704-0795802a53c1/scratchpad'
q = int(sys.argv[1])
H = gh.load(q); N = H.N
for M, T in [(4, (1,)), (10, (1, 4)), (16, (1, 4, 7)), (16, (1, 4, 10)), (26, (1, 5, 8, 12))]:
    for seed in range(2):
        rng = random.Random(seed)
        edges = [(p, L, 0, 0) for (p, L) in gh.flags(H)]
        for t in T:
            perm = list(range(N)); rng.shuffle(perm)
            edges += [(p, N + perm[p], t, 0) for p in range(N)]
        path = f'{SCR}/sd_q{q}_M{M}.txt'
        gh.write_base(path, 2 * N, M, 1, edges)
        out = subprocess.run(['./liftdiam', path, '8', '4'], capture_output=True, text=True).stdout.split('\n')[1]
        print(f'q={q} j={len(T)} M={M} T={T} seed={seed}: {out}', flush=True)
