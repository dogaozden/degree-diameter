"""j = 1 (one hop matching, degree q+2) random lift models of H(q), voltages in Z_M:
 free : random bijection, random hop labels, H(q) voltage 0;   holo: + random H(q) voltages;
 poly : constant hop voltage 1 (the n+2 cover; works up to M = 4 for any matching)."""
import random, subprocess, sys
import gh
from models import SCR

def build(q, M, model, seed, H):
    rng = random.Random(seed); N = H.N
    edges = [(p, L, rng.randrange(M) if model == 'holo' else 0, 0) for (p, L) in gh.flags(H)]
    s = list(range(N)); rng.shuffle(s)
    for p in range(N):
        edges.append((p, N + s[p], 1 if model == 'poly' else rng.randrange(1, M), 0))
    return 2 * N, edges

if __name__ == '__main__':
    q = int(sys.argv[1]); model = sys.argv[2]; Ms = [int(x) for x in sys.argv[3].split(',')]
    H = gh.load(q)
    for M in Ms:
        NB, edges = build(q, M, model, 0, H)
        path = f'{SCR}/j1_{model}_q{q}_M{M}.txt'
        gh.write_base(path, NB, M, 1, edges)
        out = subprocess.run(['./liftdiam', path, '8', '2'], capture_output=True, text=True).stdout
        print(f'q={q} j=1 model={model} M={M} unreached={out.split("unreached_pairs")[1].split()[0]}', flush=True)
