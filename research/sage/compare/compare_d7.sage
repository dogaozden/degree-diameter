r"""
Compare d7_hexagon_copies_hubs.sage with the lab's builder research/synthetic/conics2/typed_build.py (run unchanged, as a
subprocess, in 'make' mode).  typed_build.py reads the hexagon from a binary file HEXBIN (int32 q, N, #lines; the
point indices on each line; the coordinates of each point as uint8); we write that file from the Sage hexagon
(points and lines in the order of H.points / H.lines, field elements encoded as base-p digits, as typed_build's field()),
give it the same R' (file ovoid:...) and the same hub graph (file:...), read the edge list it writes, translate the vertex
numbers (copy j, kind, index x -> j*2N + kind*N + x; hubs 2NL + h and 2NL + KB + h) into Sage labels, and compare the edge sets
with the Sage graph EXACTLY.  This checks the level structure, the friendly freed sets (spread points; lines meeting v +
whiskers), sigma (Proposition 5.2), the slot order and the hubs.

Cases: q = 3 'HHH' (K=3), q = 3 'HDH' (K=3), q = 3 'HDHDH' (K=1), q = 4 'HDH' (K=3).
Run from research/sage:  sage compare/compare_d7.sage
"""
import sys, os, subprocess, tempfile
import numpy as np
HERE = os.path.abspath('.')
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
NO_AUTO_CHECK = True
load('d7_hexagon_copies_hubs.sage')
TB = os.path.join(REPO, 'research', 'synthetic', 'conics2', 'typed_build.py')
tmp = tempfile.mkdtemp(prefix='cmpd7_')


def enc(F, x):
    """base-p digit encoding of a field element (typed_build.field(): element = sum digit_i p^i for the polynomial basis 1, t, t^2...)."""
    p, e = F.characteristic(), F.degree()
    if e == 1:
        return int(x)
    co = list(x.polynomial().list()) + [0] * e
    return sum(int(co[i]) * int(p) ** i for i in range(e))


def run_case(q, types, K):
    H = hexagon(q)
    N, F = H.N, H.F
    pidx = {p: i for i, p in enumerate(H.points)}
    lidx = {Ln: i for i, Ln in enumerate(H.lines)}
    # HEXBIN
    hexfn = os.path.join(tmp, f'hex{q}.bin')
    LP = np.array([[pidx[p] for p in H.pts_on[Ln]] for Ln in H.lines], dtype=np.int32)
    X = np.array([[enc(F, x) for x in p[1:]] for p in H.points], dtype=np.uint8)
    with open(hexfn, 'wb') as f:
        f.write(np.array([q, N, len(H.lines)], dtype=np.int32).tobytes() + LP.tobytes() + X.tobytes())
    # our R' and hub graph, written for typed_build
    Rp = pairwise_opposite_points(H, K)
    ovfn = os.path.join(tmp, 'ovoid.txt')
    open(ovfn, 'w').write(' '.join(str(pidx[p]) for p in Rp) + '\n')
    he = cycle_hub_graph(K)
    hubfn = os.path.join(tmp, 'hubs.txt')
    open(hubfn, 'w').write(f'{K}\n' + ''.join(f'{a} {b}\n' for a, b in he))
    out_sol, out_edges = os.path.join(tmp, 'o.sol'), os.path.join(tmp, 'o.edges')
    res = subprocess.run([sys.executable, TB, 'make', hexfn, types, 'ovoid:' + ovfn, 'file:' + hubfn, out_sol, out_edges],
                         capture_output=True, text=True)
    if res.returncode != 0:
        print(res.stdout[-1500:], res.stderr[-1500:])
        raise RuntimeError('typed_build.py failed')
    lines_ = open(out_edges).read().split('\n')
    n_py = int(lines_[0])
    E_py = [tuple(map(int, l.split())) for l in lines_[1:] if l.strip()]
    # Sage graph built from the SAME R' and hub graph (K line-hubs, K point-hubs)
    G, data = build_d7_typed(q, types, K)
    assert data['Rp'] == Rp
    L = len(types)

    def vertex(j, e):
        s = (0 if e[0] == 0 else 1) if types[j] == 'H' else (1 if e[0] == 0 else 0)
        return (s, 'copy', j, e)

    def name(v):
        if v < 2 * N * L:
            j, rest = divmod(v, 2 * N)
            kind, x = divmod(rest, N)
            return vertex(j, H.points[x] if kind == 0 else H.lines[x])
        h = v - 2 * N * L
        return (1, 'hub', h) if h < K else (0, 'hub', h - K)
    py_edges = {frozenset((name(u), name(v))) for u, v in E_py}
    se = {frozenset(e[:2]) for e in G.edges(sort=False)}
    print(f'q={q} {types} K={K}: typed_build.py {n_py} vertices {len(py_edges)} edges; Sage {G.order()} vertices {len(se)} edges; '
          f'EXACT equal after relabelling: {py_edges == se}', flush=True)
    return py_edges == se and n_py == G.order()


ok = True
for case in ((3, 'HHH', 3), (3, 'HDH', 3), (3, 'HDHDH', 1), (4, 'HDH', 3)):
    ok &= run_case(*case)
print('compare_d7: ' + ('ALL EQUAL' if ok else 'DIFFERENCES'))
