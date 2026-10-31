# r2g: census over random G-invariant compositions with orbit-level LNS. usage: census.py GROUP m total_seconds per_pair_seconds maxorb seed
import sys, os, time, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import orb
from orb import *
from run import group_def
from lns import Comp, lns

def main():
    name, m = sys.argv[1], int(sys.argv[2])
    total = float(sys.argv[3]); per = float(sys.argv[4]); maxorb = int(sys.argv[5]); seed = int(sys.argv[6])
    G = group_from_gens(group_def(name))
    subs = all_subgroups(G); classes = conj_classes(G, subs.keys())
    sizes = [G['N']//len(K) for K in classes]
    S = Setup(G, classes)
    rng = random.Random(seed); orb.RNG = rng
    comps = compositions(sizes, m, maxorb)
    comps = [c for c in comps if any(len(classes[i]) > 1 for i in c)]
    print('group', name, 'order', G['N'], 'classes', len(classes), 'sizes', sizes, 'compositions', len(comps), flush=True)
    t0 = time.time(); best = (10**9, None, None); npairs = 0
    while time.time() - t0 < total and comps:
        A = rng.choice(comps); B = rng.choice(comps)
        if sum(sizes[c] for c in A) != sum(sizes[c] for c in B): continue
        comp = Comp(S, A, B)
        if not comp.feasible: continue
        r = comp.complete([], rng)
        if r is None: continue
        npairs += 1
        dl = time.time() + per
        res = lns(comp, rng, 10**9, 3.0, 0.3, dl, kmax=3)
        if res is None: continue
        (bf, bev), acc, tries, fails = res
        if bf < best[0]:
            best = (bf, (A, B), bev)
            print('  new best far %d  A=%s B=%s  (pairs so far %d, t=%.0f)' % (bf, [sizes[c] for c in A], [sizes[c] for c in B], npairs, time.time()-t0), flush=True)
            with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'out', 'census_%s_m%d.edges' % (name, m)), 'w') as fh:
                fh.write('%d\n' % (2*m))
                for (x, y) in bev: fh.write('%d %d\n' % (x, y))
    print('RESULT group=%s m=%d n=%d pairs=%d best_far=%s' % (name, m, 2*m, npairs, best[0]), flush=True)

if __name__ == '__main__':
    main()
