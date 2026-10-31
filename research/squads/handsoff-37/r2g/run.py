import sys, time, random, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from orb import *

def perm_from_cycles(n, cycles):
    p = list(range(n))
    for c in cycles:
        for i in range(len(c)):
            p[c[i]] = c[(i+1) % len(c)]
    return tuple(p)

def group_def(name):
    if name == 'psl27':   # PSL(2,7) on P^1(F7), points 0..6, inf=7
        t = tuple([(i+1) % 7 for i in range(7)] + [7])
        s = [0]*8
        s[0] = 7; s[7] = 0
        for i in range(1, 7): s[i] = (-pow(i, 5, 7)) % 7
        return [t, tuple(s)]
    if name == 'pgl27':
        t, s = group_def('psl27')
        u = tuple([(3*i) % 7 for i in range(7)] + [7])
        return [t, s, u]
    if name == 'a5':
        return [perm_from_cycles(5, [(0, 1, 2)]), perm_from_cycles(5, [(0, 1, 2, 3, 4), ]) if False else perm_from_cycles(5, [(0,1,2,3,4)])] 
    if name == 's4':
        return [perm_from_cycles(4, [(0, 1)]), perm_from_cycles(4, [(0, 1, 2, 3)])]
    if name == 'a4':
        return [perm_from_cycles(4, [(0, 1, 2)]), perm_from_cycles(4, [(0, 1), (2, 3)])]
    if name == 's5':
        return [perm_from_cycles(5, [(0, 1)]), perm_from_cycles(5, [(0, 1, 2, 3, 4)])]
    if name == 'a5b':
        return [perm_from_cycles(5, [(0, 1, 2)]), perm_from_cycles(5, [(1, 2, 3, 4)]) ]
    if name == 's3':
        return [perm_from_cycles(3, [(0, 1)]), perm_from_cycles(3, [(0, 1, 2)])]
    if name == 'd4':
        return [perm_from_cycles(4, [(0, 1, 2, 3)]), perm_from_cycles(4, [(0, 2)])]
    if name == 'v4':
        return [perm_from_cycles(4, [(0, 1), (2, 3)]), perm_from_cycles(4, [(0, 2), (1, 3)])]
    if name == 'z2':
        return [perm_from_cycles(2, [(0, 1)])]
    if name == 'z3':
        return [perm_from_cycles(3, [(0, 1, 2)])]
    if name == 'z6':
        return [perm_from_cycles(5, [(0, 1, 2), (3, 4)])]
    raise SystemExit('unknown group ' + name)

def main():
    name = sys.argv[1]; ms = [int(x) for x in sys.argv[2].split(',')]
    budget = float(sys.argv[3]) if len(sys.argv) > 3 else 300.0
    cap = int(sys.argv[4]) if len(sys.argv) > 4 else 20000
    maxorb = int(sys.argv[5]) if len(sys.argv) > 5 else 6
    gens = group_def(name)
    G = group_from_gens(gens)
    subs = all_subgroups(G)
    classes = conj_classes(G, subs.keys())
    sizes = [G['N']//len(K) for K in classes]
    print('group', name, 'order', G['N'], 'subgroups', len(subs), 'classes', len(classes), file=sys.stderr)
    print('class orders (|K|, index):', sorted(zip([len(K) for K in classes], sizes)), file=sys.stderr)
    import orb
    orb.RNG = random.Random(int(os.environ.get('SEED', '7')))
    S = Setup(G, classes)
    free = [i for i, K in enumerate(classes) if len(K) == 1]
    t0 = time.time()
    overall = {}
    for m in ms:
        comps = compositions(sizes, m, maxorb)
        comps = [c for c in comps if any(len(classes[i]) > 1 for i in c)]
        print('m', m, 'side compositions', len(comps), file=sys.stderr, flush=True)
        pairs = [(a, b) for a in range(len(comps)) for b in range(a, len(comps))]
        random.Random(1).shuffle(pairs)
        bestm = (10**9, None); total_sol = 0; ncomp = 0
        deadline_all = time.time() + budget
        for (a, b) in pairs:
            if time.time() > deadline_all: break
            ncomp += 1
            dl = min(deadline_all, time.time() + 20)
            r = solve_composition(S, comps[a], comps[b], cap, dl)
            if r[0] == 0 and r[1] is None:
                continue
            nsol, bf, bev = r[0], r[1], r[2]
            total_sol += nsol
            if bf is not None and bf < bestm[0]:
                bestm = (bf, (comps[a], comps[b], bev))
                print('  m=%d new best far %d  A=%s B=%s sols=%d' % (m, bf, [name+str(sizes[c]) for c in comps[a]], [sizes[c] for c in comps[b]], nsol), file=sys.stderr, flush=True)
                n = 2*m
                with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'out', 'best_%s_m%d.edges' % (name, m)), 'w') as fh:
                    fh.write('%d\n' % n)
                    for (x, y) in bev: fh.write('%d %d\n' % (x, y))
        print('RESULT group=%s m=%d n=%d comps_tried=%d sols=%d best_far=%s time=%.1f' % (name, m, 2*m, ncomp, total_sol, bestm[0], time.time()-t0), flush=True)

if __name__ == '__main__':
    main()
