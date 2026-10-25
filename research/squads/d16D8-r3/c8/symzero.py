# symzero.py (card c8, wildcard): C-invariant Z_m-lifts of H(q) with STRUCTURED voltages.
# Base graph = I(H(q)) + two C-equivariant perfect matchings (points -> lines), as in symbase.py, but the flag
# (incidence) voltages are chosen by MODE:
#   zero  : all flag voltages 0, so the lift starts as m disjoint copies of I(H(q)) (the picture in the DGQ description);
#           only the matching orbits carry voltages (use FIXCLS = number of flag orbits in symrepair to keep flags at 0)
#   rand  : random flag voltages (identical to symbase.py)
#   shiftr: as shift but flag voltages random
#   shift : flags 0; M2(p) = g^K2(M1(p)), i.e. the second matching is the first composed with a fixed power of the
#           generator; V2=same copies the M1 voltage of each point orbit to M2, V2=free draws new ones
#   python3 symzero.py Q GROUP.json m seed OUT.base OUT.src MODE
# Edge classes: flag orbits 0..F-1, then matching-1 orbits, then matching-2 orbits (class = orbit id, as in symbase.py).
import sys, json, random, struct, os
D16 = '/home/user/degree-diameter/research/d16D8'

def hex_poly(q):
    b = open(os.path.join(D16, 'hex', 'hex_q%d.bin' % q), 'rb').read()
    q_, N, L = struct.unpack('<3i', b[:12])
    lp = struct.unpack('<%di' % (L * (q + 1)), b[12:12 + 4 * L * (q + 1)])
    return N, [tuple(lp[i * (q + 1):(i + 1) * (q + 1)]) for i in range(L)]

def orbits(perm):
    seen = [-1] * len(perm); reps = []
    for x in range(len(perm)):
        if seen[x] >= 0: continue
        o = []; y = x
        while seen[y] < 0: seen[y] = len(reps); o.append(y); y = perm[y]
        reps.append(o)
    return reps, seen

def main():
    q, gfile, m, seed, out, srcout, mode = int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), sys.argv[5], sys.argv[6], sys.argv[7]
    K2 = int(os.environ.get('K2', '1')); V2 = os.environ.get('V2', 'free')
    G = json.load(open(gfile)); rnd = random.Random(seed)
    N, lines = hex_poly(q); pt, ln, r = G['pt'], G['ln'], G['r']
    porb, pof = orbits(pt); lorb, lof = orbits(ln)
    assert all(len(o) == r for o in porb) and all(len(o) == r for o in lorb), 'not semiregular'
    edges = []; oid = 0; fid = {}
    for l, L in enumerate(lines):
        for p in L:
            if (p, l) in fid: continue
            c = rnd.randrange(m) if mode in ('rand', 'shiftr') else 0
            x, y = p, l
            for _ in range(r):
                fid[(x, y)] = oid; edges.append((x, N + y, c, oid)); x, y = pt[x], ln[y]
            oid += 1
    F = oid
    def matching(cls_start, volts=None):
        # equivariant random matching: point orbit i -> line orbit perm[i], alignment random, voltage per orbit
        perm = list(range(len(lorb))); rnd.shuffle(perm)
        M = {}; cl = cls_start; vol = {}
        for i, o in enumerate(porb):
            p0 = o[0]; l0 = lorb[perm[i]][rnd.randrange(r)]
            c = rnd.randrange(m) if volts is None else volts[i]
            vol[i] = c
            x, y = p0, l0
            for _ in range(r):
                M[x] = y; edges.append((x, N + y, c, cl)); x, y = pt[x], ln[y]
            cl += 1
        return M, vol, cl
    M1, v1, oid = matching(oid)
    if mode in ('shift', 'shiftr'):
        lnk = list(range(len(ln)))
        for _ in range(K2):
            lnk = [ln[x] for x in lnk]
        # M2(p) = ln^K2 (M1(p)); equivariant because ln^K2 commutes with ln
        vols = [v1[i] for i in range(len(porb))] if V2 == 'same' else None
        M2 = {p: lnk[M1[p]] for p in M1}
        # rebuild the second matching's edges with its own class ids
        cl = oid
        for i, o in enumerate(porb):
            c = v1[i] if V2 == 'same' else ((-v1[i]) % m if V2 == 'neg' else rnd.randrange(m))
            for x in o:
                edges.append((x, N + M2[x], c, cl))
            cl += 1
        oid = cl
    else:
        _, _, oid = matching(oid)
    V = 2 * N
    bad = sum(1 for (x, y, c, cl) in edges if cl >= F and x == y - N and False)
    with open(out, 'w') as f:
        f.write('%d %d %d\n' % (V, m, len(edges)))
        f.write(''.join('%d %d %d %d\n' % e for e in edges))
    with open(srcout, 'w') as f:
        f.write('\n'.join(str(o[0]) for o in porb) + '\n' + '\n'.join(str(N + o[0]) for o in lorb) + '\n')
    print('mode=%s N=%d r=%d flag orbits F=%d, total classes %d, edges %d, sources %d' % (mode, N, r, F, oid, len(edges), len(porb) + len(lorb)))

main()
