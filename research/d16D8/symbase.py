# symbase.py: random C-invariant designs (I + 2 matchings, Z_m voltages) for a polygon with a semiregular cyclic
# collineation group C = <g>, as base files for symrepair / baselift.
#
# Every edge orbit under C gets one voltage, so C acts on the lift and BFS from one point and one line of each C-orbit
# (the SRC file) decides the diameter exactly. Matchings are C-equivariant: a random bijection between point orbits
# and line orbits plus a random alignment, M(g^i p0) = g^(i+a) l0. Edge class field = orbit id (symrepair keeps all
# edges of an orbit at the same voltage).
#
#   python3 symbase.py hex q GROUP.json m seed OUT.base OUT.src      (GROUP from hexsym.py)
#   python3 symbase.py gq  q GROUP.json m seed OUT.base OUT.src      (GROUP: {"S": 4x4 matrix over F_q, "d": order})
import sys, json, random, struct

def hex_poly(q):
    b = open('/home/user/degree-diameter/research/d16D8/hex/hex_q%d.bin' % q, 'rb').read()
    q_, N, L = struct.unpack('<3i', b[:12])
    lp = struct.unpack('<%di' % (L * (q + 1)), b[12:12 + 4 * L * (q + 1)])
    return N, [tuple(lp[i * (q + 1):(i + 1) * (q + 1)]) for i in range(L)]

def gq_group(q, G):
    sys.path.insert(0, '/home/user/degree-diameter/research/d16D8'); import gq
    P = gq.load(q); N = P['N']; S = G['S']
    idx = {p: i for i, p in enumerate(P['pts'])}
    def norm(v):
        for x in v:
            if x % q:
                s = pow(x % q, q - 2, q); return tuple(y * s % q for y in v)
    pt = [idx[norm([sum(S[i][t] * v[t] for t in range(4)) for i in range(4)])] for v in P['pts']]
    lidx = {tuple(L): i for i, L in enumerate(P['lines'])}
    ln = [lidx[tuple(sorted(pt[p] for p in L))] for L in P['lines']]
    return N, [tuple(L) for L in P['lines']], pt, ln, G['d']

def orbits(perm):
    seen = [-1] * len(perm); reps = []
    for x in range(len(perm)):
        if seen[x] >= 0: continue
        o = []; y = x
        while seen[y] < 0: seen[y] = len(reps); o.append(y); y = perm[y]
        reps.append(o)
    return reps, seen

def main():
    kind, q, gfile, m, seed, out, srcout = sys.argv[1], int(sys.argv[2]), sys.argv[3], int(sys.argv[4]), int(sys.argv[5]), sys.argv[6], sys.argv[7]
    G = json.load(open(gfile)); rnd = random.Random(seed)
    if kind == 'hex':
        N, lines = hex_poly(q); pt, ln, r = G['pt'], G['ln'], G['r']
    else:
        N, lines, pt, ln, r = gq_group(q, G)
    porb, pof = orbits(pt); lorb, lof = orbits(ln)
    assert all(len(o) == r for o in porb) and all(len(o) == r for o in lorb), 'not semiregular'
    edges = []; oid = 0
    # flag orbits
    fid = {}
    for l, L in enumerate(lines):
        for p in L:
            if (p, l) in fid: continue
            c = rnd.randrange(m); x, y = p, l
            for _ in range(r):
                fid[(x, y)] = oid; edges.append((x, N + y, c, oid)); x, y = pt[x], ln[y]
            oid += 1
    assert len(edges) == N * (len(lines[0]))
    # equivariant matchings
    for k in range(2):
        perm = list(range(len(lorb))); rnd.shuffle(perm)
        for i, o in enumerate(porb):
            p0 = o[0]; l0 = lorb[perm[i]][rnd.randrange(r)]; c = rnd.randrange(m)
            x, y = p0, l0
            for _ in range(r):
                edges.append((x, N + y, c, oid)); x, y = pt[x], ln[y]
            oid += 1
    with open(out, 'w') as f:
        f.write('%d %d %d\n' % (2 * N, m, len(edges)))
        f.write(''.join('%d %d %d %d\n' % e for e in edges))
    with open(srcout, 'w') as f:
        f.write('\n'.join(str(o[0]) for o in porb) + '\n' + '\n'.join(str(N + o[0]) for o in lorb) + '\n')
    print('N=%d r=%d point orbits %d, edge orbits %d, sources %d' % (N, r, len(porb), oid, len(porb) + len(lorb)))

main()
