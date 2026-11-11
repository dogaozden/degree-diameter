import sys, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/raise9/r3/w08')
from coset import run
specs = sys.argv[1].split('|')
n = int(sys.argv[2]); Delta = int(sys.argv[3]); D = int(sys.argv[4])
for sp in specs:
    t0 = time.time()
    best, hits, cnt, reg, nreps = run(sp, n, Delta, D)
    print(sp, 'n=%d' % n, 'invclasses=%d' % nreps, 'cands=%d regular=%d' % (cnt, reg),
          'best=%s' % (best[0] if best else None), 'hits<=%d: %d' % (D, len(hits)), 'time=%.1f' % (time.time()-t0), flush=True)
    if hits:
        print('HIT', hits[0], flush=True)
