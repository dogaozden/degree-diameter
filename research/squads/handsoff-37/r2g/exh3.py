# r2g: EXHAUSTIVE over all G-invariant cubic bipartite graphs whose sides have at most K orbits each.
# usage: exh3.py GROUP m K budget_seconds   (GROUP: psl27 | h252 | s4 | a5 | pgl27 ...)
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import orb
from orb import *
from run import group_def
import hcensus

def get_group(name):
    if name == 'h252':
        gens = hcensus.gen_pair(hcensus.H)
        return group_from_gens(gens)
    return group_from_gens(group_def(name))

def main():
    name = sys.argv[1]; m = int(sys.argv[2]); K = int(sys.argv[3]); budget = float(sys.argv[4])
    G = get_group(name)
    subs = all_subgroups(G); classes = conj_classes(G, subs.keys())
    sizes = [G['N']//len(K_) for K_ in classes]
    S = Setup(G, classes)
    print('group', name, 'order', G['N'], 'classes', len(classes), flush=True)
    comps = compositions(sizes, m, K)
    comps = [c for c in comps if any(len(classes[i]) > 1 for i in c)]
    # unordered pairs A <= B (sides are symmetric)
    pairs = [(a, b) for a in range(len(comps)) for b in range(a, len(comps))]
    print('compositions', len(comps), 'pairs', len(pairs), flush=True)
    t0 = time.time(); best = (10**9, None, None, None); tot = 0; feas = 0; done = 0
    for (a, b) in pairs:
        if time.time() - t0 > budget:
            print('BUDGET STOP after', done, 'pairs', flush=True); break
        done += 1
        r = solve_composition(S, comps[a], comps[b], 200000, time.time() + 60)
        if r[1] is None: continue
        nsol, bf, bev = r[0], r[1], r[2]
        feas += 1; tot += nsol
        if bf < best[0]:
            best = (bf, [sizes[c] for c in comps[a]], [sizes[c] for c in comps[b]], bev)
            print('  best far %d  A=%s B=%s' % (bf, best[1], best[2]), flush=True)
            with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'out', 'exh3_%s_m%d_K%d.edges' % (name, m, K)), 'w') as fh:
                fh.write('%d\n' % (2*m))
                for (x, y) in bev: fh.write('%d %d\n' % (x, y))
    print('RESULT group=%s m=%d n=%d K=%d pairs_done=%d feasible=%d graphs=%d best_far=%s time=%.0f' % (
        name, m, 2*m, K, done, feas, tot, best[0], time.time()-t0), flush=True)

if __name__ == '__main__':
    main()
