"""Score Z_M lifts of H(3) + 2 hop matchings with random flag voltages and random hop labels (liftdiam, D=8, all sources).
usage: lifts.py variant Mlo Mhi seeds [perm files...]
 variant R: two random matchings; A: two annealed matchings (files given); B: annealed + random matching.
"""
import random
import subprocess
import sys
import time

sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d8')
import gh  # noqa: E402

H = gh.load(3)
N = H.N
FLAGS = gh.flags(H)
LIFTDIAM = '/home/user/degree-diameter/research/theorems/d8/liftdiam'
HERE = '/home/user/degree-diameter/research/squads/r2-d8/d5'


def read_perm(path):
    return [int(x) for x in open(path).read().split()]


def lift_unreached(M, hops, rng, tmp, D=8):
    edges = [(p, L, rng.randrange(M), 0) for (p, L) in FLAGS]
    for s in hops:
        edges += [(p, N + s[p], rng.randrange(M), 0) for p in range(N)]
    gh.write_base(tmp, 2 * N, M, 1, edges)
    out = subprocess.run([LIFTDIAM, tmp, str(D), '1', '1'], capture_output=True, text=True).stdout
    return int(out.split('unreached_pairs')[1].split()[0])


def main():
    variant = sys.argv[1]
    Mlo, Mhi, seeds = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    fixed = [read_perm(f) for f in sys.argv[5:]]
    tmp = f'{HERE}/tmp_lift_{variant}.txt'
    results = {}
    for M in range(Mlo, Mhi + 1):
        unr = []
        t0 = time.time()
        for sd in range(seeds):
            rng = random.Random(1000 * M + sd)
            if variant == 'R':
                hops = []
                for _ in range(2):
                    perm = list(range(N)); rng.shuffle(perm); hops.append(perm)
            elif variant == 'A':
                hops = fixed[:2]
            elif variant == 'B':
                perm = list(range(N)); rng.shuffle(perm)
                hops = [fixed[0], perm]
            unr.append(lift_unreached(M, hops, rng, tmp))
        zeros = sum(1 for u in unr if u == 0)
        results[M] = (zeros, min(unr))
        print(f'variant={variant} M={M} seeds={seeds} zero_hits={zeros} min_unreached={min(unr)} median={sorted(unr)[len(unr)//2]} time={time.time()-t0:.1f}s', flush=True)
    ok = [M for M, (z, _) in results.items() if z > 0]
    print(f'variant={variant} largest_M_with_unreached_0 = {max(ok) if ok else None}', flush=True)


if __name__ == '__main__':
    main()
