# twbuild.py (card c7, d16D8 round 3): TWISTED C'-invariant Z_m lift designs, from research/d16D8/symbase.py.
#
# C' = <h>, h = g^SUB for the generator g of the group file (SUB = 1: the whole group). r = order of h (semiregular).
# Voltages: edge h^j e0 of an orbit gets U^j * c_o (mod m), U a unit with U^r = 1 mod m (U = 1: untwisted, symbase).
# Matchings are C'-equivariant with the same twist. Edge orbit id = cls, position j = pos.
#
#   python3 twbuild.py hex q GROUP.json SUB m U seed OUT.b5 OUT.src
#   python3 twbuild.py gq  q GROUP.json SUB m U seed OUT.b5 OUT.src
#
# OUT.b5 first line: "V m E U", then E lines "x y c cls pos" (read by twrepair). OUT.src: C'-orbit representatives.
import sys, json, random, struct

D16 = '/home/user/degree-diameter/research/d16D8'

def hex_poly(q):
    b = open(D16 + '/hex/hex_q%d.bin' % q, 'rb').read()
    q_, N, L = struct.unpack('<3i', b[:12])
    lp = struct.unpack('<%di' % (L * (q + 1)), b[12:12 + 4 * L * (q + 1)])
    return N, [tuple(lp[i * (q + 1):(i + 1) * (q + 1)]) for i in range(L)]

def gq_group(q, G):
    sys.path.insert(0, D16); import gq
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

def power_perm(perm, e):
    res = list(range(len(perm)))
    for _ in range(e):
        res = [perm[x] for x in res]
    return res

def orbits(perm):
    seen = [-1] * len(perm); reps = []
    for x in range(len(perm)):
        if seen[x] >= 0: continue
        o = []; y = x
        while seen[y] < 0: seen[y] = len(reps); o.append(y); y = perm[y]
        reps.append(o)
    return reps, seen

def main():
    kind, q, gfile = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    sub, m, u, seed = int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6]), int(sys.argv[7])
    out5, srcout = sys.argv[8], sys.argv[9]
    G = json.load(open(gfile)); rnd = random.Random(seed)
    if kind == 'hex':
        N, lines = hex_poly(q); pt, ln = G['pt'], G['ln']
    else:
        N, lines, pt, ln, _ = gq_group(q, G)
    pt = power_perm(pt, sub); ln = power_perm(ln, sub)
    porb, pof = orbits(pt); lorb, lof = orbits(ln)
    r = len(porb[0])
    assert all(len(o) == r for o in porb) and all(len(o) == r for o in lorb), 'not semiregular'
    assert pow(u, r, m) == 1, 'U^r must be 1 mod m'
    upow = [pow(u, j, m) for j in range(r)]
    edges = []; oid = 0; fid = {}
    for l, L in enumerate(lines):
        for p in L:
            if (p, l) in fid: continue
            c = rnd.randrange(m); x, y = p, l
            for j in range(r):
                fid[(x, y)] = oid; edges.append((x, N + y, upow[j] * c % m, oid, j)); x, y = pt[x], ln[y]
            oid += 1
    assert len(edges) == N * len(lines[0]), (len(edges), N)
    for k in range(2):
        perm = list(range(len(lorb))); rnd.shuffle(perm)
        for i, o in enumerate(porb):
            p0 = o[0]; l0 = lorb[perm[i]][rnd.randrange(r)]; c = rnd.randrange(m)
            x, y = p0, l0
            for j in range(r):
                edges.append((x, N + y, upow[j] * c % m, oid, j)); x, y = pt[x], ln[y]
            oid += 1
    with open(out5, 'w') as f:
        f.write('%d %d %d %d\n' % (2 * N, m, len(edges), u))
        f.write(''.join('%d %d %d %d %d\n' % e for e in edges))
    with open(srcout, 'w') as f:
        f.write('\n'.join(str(o[0]) for o in porb) + '\n' + '\n'.join(str(N + o[0]) for o in lorb) + '\n')
    print('N=%d r=%d m=%d U=%d point orbits %d, edge orbits %d, sources %d, edges %d' % (
        N, r, m, u, len(porb), oid, len(porb) + len(lorb), len(edges)))

main()
