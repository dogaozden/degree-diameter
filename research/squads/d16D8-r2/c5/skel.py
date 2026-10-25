# c5: level skeletons (L, t1, t2) for Z_m lifts of I(W(q)) + 2 matchings, m = L*k, gcd(L,k) = 1.
# Flags get voltage 0 mod L, matching 1 gets t1 mod L, matching 2 gets t2 mod L; the sheet part c // L is free.
# Usage: python3 skel.py gen q L t1 t2 k seed OUT
import sys, os, json, random
sys.path.insert(0, '/home/user/degree-diameter/research/d16D8')
import gq

HERE = os.path.dirname(os.path.abspath(__file__))

def flags_cache(q):
    fn = os.path.join(HERE, 'designs', 'flags_q%d.json' % q)
    if os.path.exists(fn):
        d = json.load(open(fn))
        return d['N'], [tuple(e) for e in d['flags']]
    G = gq.load(q); N = G['N']
    flags = [(p, N + l) for l, L in enumerate(G['lines']) for p in L]
    json.dump({'N': N, 'flags': flags}, open(fn, 'w'))
    return N, flags

def make_design(q, L, t1, t2, k, seed, out):
    N, flags = flags_cache(q)
    rnd = random.Random(seed)
    edges = []
    for (p, l) in flags:                       # flags: level 0, free sheet
        edges.append((p, l, L * rnd.randrange(k), 1))
    for cls, t in ((100, t1), (101, t2)):      # matchings points -> lines, level t, free sheet
        perm = list(range(N)); rnd.shuffle(perm)
        for p in range(N):
            edges.append((p, N + perm[p], t + L * rnd.randrange(k), cls))
    gq.write_base(out, 2 * N, L * k, edges)
    return out

if __name__ == '__main__':
    if sys.argv[1] == 'gen':
        q, L, t1, t2, k, seed = map(int, sys.argv[2:8])
        print(make_design(q, L, t1, t2, k, seed, sys.argv[8]))
