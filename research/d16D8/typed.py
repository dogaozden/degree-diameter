# typed.py: base multigraphs for baselift (Z_k lifts) built from levels of H(q) and its dual H^D.
#
# Level j in Z_L has a type 'H' or 'D'. Every level is a copy of the incidence graph I of H(q); base vertex
# j*2N + x, x = point (0..N-1) or line (N + l). Side A of an H level = points, of a D level = lines.
# For each shift t in T, each A-element a of level j has one edge to a B-element of level j+t:
#   friendly (types differ): the same hexagon element (identity), class 2 (voltage movable, never swapped);
#   unfriendly (same type): a bijection (random unless given), class 100 + transition index (swappable).
# Flag edges get class 1 (voltage movable) or 0 (fixed) with FLAGS=fixed.
# Voltages in Z_k: VOLT=rand (default) or zero.
#
#   python3 typed.py HEXFILE TYPES T k seed OUT        e.g.  typed.py hex/hex_q3.bin HDHDH 1,2 4 1 runs/t.base
# env: VOLT=rand|zero, FLAGVOLT=rand|zero, FLAGS=movable|fixed, ALLRANDOM=1 (bijections even when friendly)
import sys, os, random, struct

def load_hex(fn):
    b = open(fn, 'rb').read()
    q, N, L = struct.unpack('<3i', b[:12])
    lp = struct.unpack('<%di' % (L * (q + 1)), b[12:12 + 4 * L * (q + 1)])
    lines = [lp[i * (q + 1):(i + 1) * (q + 1)] for i in range(L)]
    return q, N, lines

def build(hexfile, types, T, k, seed):
    random.seed(seed)
    q, N, lines = load_hex(hexfile)
    L = len(types)
    V = L * 2 * N
    volt = os.environ.get('VOLT', 'rand')
    fvolt = os.environ.get('FLAGVOLT', volt)
    fcls = 0 if os.environ.get('FLAGS', 'movable') == 'fixed' else 1
    allrandom = os.environ.get('ALLRANDOM') == '1'
    rv = (lambda: random.randrange(k)) if volt == 'rand' else (lambda: 0)
    rf = (lambda: random.randrange(k)) if fvolt == 'rand' else (lambda: 0)
    edges = []
    for j in range(L):
        base = j * 2 * N
        for l, pts in enumerate(lines):
            for p in pts:
                edges.append((base + p, base + N + l, rf(), fcls))
    tr = 0
    for j in range(L):
        for t in T:
            j2 = (j + t) % L
            Aoff = 0 if types[j] == 'H' else N          # A side of level j: points (H) or lines (D)
            Boff = N if types[j2] == 'H' else 0         # B side of level j2: lines (H) or points (D)
            friendly = types[j] != types[j2]
            if friendly and not allrandom:
                perm = list(range(N)); cls = 2
            else:
                perm = list(range(N)); random.shuffle(perm); cls = 100 + tr
            for a in range(N):
                edges.append((j * 2 * N + Aoff + a, j2 * 2 * N + Boff + perm[a], rv(), cls))
            tr += 1
    return V, edges

def write(fn, V, k, edges):
    with open(fn, 'w') as f:
        f.write('%d %d %d\n' % (V, k, len(edges)))
        for e in edges:
            f.write('%d %d %d %d\n' % e)

if __name__ == '__main__':
    hexfile, types, T, k, seed, out = sys.argv[1], sys.argv[2], [int(x) for x in sys.argv[3].split(',')], int(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
    V, edges = build(hexfile, types, T, k, seed)
    write(out, V, k, edges)
    print('V=%d E=%d k=%d types=%s T=%s' % (V, len(edges), k, types, T))
