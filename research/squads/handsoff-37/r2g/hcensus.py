# r2g: census of random H-invariant graphs, H = colour-preserving automorphisms of conder168 (order 252),
# compositions sampled at random (no fixed points), orbit-level LNS. usage: hcensus.py m total per_pair seed
import sys, os, time, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import orb
from orb import *
from lns import Comp, lns
from collections import deque
SQ = '/home/user/degree-diameter/research/squads/handsoff-37/'
toks = open(SQ + 'shared/seeds/conder168.edges').read().split()
n0 = int(toks[0]); N0 = [[] for _ in range(n0)]
for i in range(1, len(toks), 2):
    a, b = int(toks[i]), int(toks[i+1]); N0[a].append(b); N0[b].append(a)
col = [-1]*n0; col[0] = 0; dq = deque([0])
while dq:
    x = dq.popleft()
    for y in N0[x]:
        if col[y] < 0: col[y] = 1 - col[x]; dq.append(y)
lines = open(SQ + 'c5/out/aut168.txt').read().split('\n')
auts = [tuple(int(x) for x in l.split()) for l in lines[1:] if l.strip()]
H = [p for p in auts if all(col[p[v]] == col[v] for v in range(n0))]
def gen_pair(H):
    rng = random.Random(0)
    while True:
        a, b = rng.sample(H, 2)
        if len(closure_perm([a, b])) == len(H): return [a, b]
def closure_perm(gens):
    e = tuple(range(len(gens[0]))); S = {e}; fr = [e]
    while fr:
        new = []
        for x in fr:
            for g in gens:
                y = pmul(x, g)
                if y not in S: S.add(y); new.append(y)
        fr = new
    return S
def main():
    m = int(sys.argv[1]); total = float(sys.argv[2]); per = float(sys.argv[3]); seed = int(sys.argv[4])
    gens = gen_pair(H)
    G = group_from_gens(gens)
    subs = all_subgroups(G); classes = conj_classes(G, subs.keys())
    sizes = [G['N']//len(K) for K in classes]
    print('H order', G['N'], 'subgroups', len(subs), 'classes', len(classes), 'orbit sizes', sorted(sizes), flush=True)
    S = Setup(G, classes)
    rng = random.Random(seed); orb.RNG = rng
    allowed = [i for i, s in enumerate(sizes) if s > 1]
    t0 = time.time(); best = (10**9, None); npairs = 0; ncomp = 0
    def rand_comp():
        while True:
            rem = m; comp = []
            while rem > 0:
                ok = [i for i in allowed if sizes[i] <= rem]
                if not ok: break
                c = rng.choice(ok); comp.append(c); rem -= sizes[c]
                if len(comp) > 14: break
            if rem == 0: return comp
    while time.time() - t0 < total:
        A = rand_comp(); B = rand_comp()
        if A is None or B is None: continue
        ncomp += 1
        comp = Comp(S, A, B)
        if not comp.feasible: continue
        r = comp.complete([], rng)
        if r is None: continue
        npairs += 1
        res = lns(comp, rng, 10**9, 3.0, 0.3, time.time() + per, kmax=3)
        if res is None: continue
        (bf, bev), acc, tries, fails = res
        if bf < best[0]:
            best = (bf, bev)
            print('  new best far %d  A=%s B=%s (feasible pairs %d, t=%.0f)' % (bf, sorted(sizes[c] for c in A), sorted(sizes[c] for c in B), npairs, time.time()-t0), flush=True)
            with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'out', 'hcensus_m%d_s%d.edges' % (m, seed)), 'w') as fh:
                fh.write('%d\n' % (2*m))
                for (x, y) in bev: fh.write('%d %d\n' % (x, y))
    print('RESULT H252 m=%d n=%d feasible_pairs=%d sampled=%d best_far=%s' % (m, 2*m, npairs, ncomp, best[0]), flush=True)
if __name__ == '__main__':
    main()
