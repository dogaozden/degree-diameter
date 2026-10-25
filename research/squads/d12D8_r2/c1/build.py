#!/usr/bin/env python3
"""c1/build.py: Gomez's Omega-B1 (thesis sec. 2.9.3, figs 2.21a/b) for B1 = incidence graph of H(q), as read by card c1.

Reading of the figures (see c1/READING.txt):
- alpha = (q+3)/2, so Delta_1 + 2 = 2*alpha. There are G = 5*alpha copies of B1, numbered c = 5*g + i,
  group g in 0..alpha-1, position i in Z_5 (the five copies drawn on the circle, in figure order).
- B1 vertices: point p -> p, line l -> n + l (n = #points = #lines = (q^6-1)/(q-1)); N1 = 2n.
- Every copy vertex is a port for exactly one tuple k in [n]: the points are "outer" ports (side A, the
  vertices sitting on the big circle in fig. 2.21), the lines are "inner" ports (side B, the vertices on the
  pentagram). The port of tuple k in copy c is phi_c(k) (outer) and psi_c(k) (inner).
- Each tuple k carries 10 new vertices (copies of K1): U_j and B_j for j in Z_5 (fig. labels j and j-bar).
- Group pattern 'a' (fig. 2.21a): U_j (inner-type) is joined to the inner ports of copies j-1 and j+1 of the group;
  B_j (outer-type) to the outer ports of copies j+2 and j+3.
- Group pattern 'b' (fig. 2.21b): U_j (outer-type) is joined to the outer ports of copies j+3 and j+4;
  B_j (inner-type) to the inner ports of copies j-1 and j+1.
- Each new vertex gets 2 neighbours per group, so degree 2*alpha; each copy vertex gets 2 new neighbours.

Usage:
  python3 build.py build Q PATTERN SIDE MAPS OUT      (writes edge list: "N" then "a b" lines)
  python3 build.py analyze Q PATTERN SIDE MAPS         (scipy all-pairs: diameter and per-class maxima, q small)
PATTERN: string of alpha letters from {a,b}. SIDE: P (outer ports are points) or L (outer ports are lines).
MAPS: id (phi(k)=point k, psi(k)=line k in every copy), rand:SEED (psi random, phi=id, same in every copy),
      both:SEED (phi and psi random, same in every copy), copy:SEED (phi_c, psi_c random for each copy c).
"""
import sys
import numpy as np

sys.path.insert(0, '/home/user/degree-diameter/research/d12D8/tools')
from hexlib import load_hex


def port_maps(n, G, maps):
    """Return phi, psi as int arrays of shape (G, n): phi[c][k] = point (outer port), psi[c][k] = line index."""
    if maps == 'id':
        phi = np.tile(np.arange(n), (G, 1))
        psi = np.tile(np.arange(n), (G, 1))
    elif maps.startswith('rand:'):
        rng = np.random.default_rng(int(maps.split(':')[1]))
        phi = np.tile(np.arange(n), (G, 1))
        psi = np.tile(rng.permutation(n), (G, 1))
    elif maps.startswith('both:'):
        rng = np.random.default_rng(int(maps.split(':')[1]))
        phi = np.tile(rng.permutation(n), (G, 1))
        psi = np.tile(rng.permutation(n), (G, 1))
    elif maps.startswith('copy:'):
        rng = np.random.default_rng(int(maps.split(':')[1]))
        phi = np.array([rng.permutation(n) for _ in range(G)])
        psi = np.array([rng.permutation(n) for _ in range(G)])
    else:
        raise ValueError(maps)
    return phi, psi


# (group pattern, label j in Z5, kind) -> (kind of port, relative copies)
# label kinds: 'U' = unbarred label j, 'B' = barred label j-bar.
def label_rule(pat, kind, j):
    if pat == 'a':
        if kind == 'U':
            return 'inner', [(j - 1) % 5, (j + 1) % 5]
        return 'outer', [(j + 2) % 5, (j + 3) % 5]
    if pat == 'b':
        if kind == 'U':
            return 'outer', [(j + 3) % 5, (j + 4) % 5]
        return 'inner', [(j - 1) % 5, (j + 1) % 5]
    raise ValueError(pat)


def build(q, pattern, side, maps):
    n, lines = load_hex(q)
    lines = np.asarray(lines)
    alpha = (q + 3) // 2
    assert len(pattern) == alpha, (pattern, alpha)
    G = 5 * alpha
    N1 = 2 * n
    base_edges = []
    for l in range(n):
        for p in lines[l]:
            base_edges.append((int(p), n + l))
    base_edges = np.array(base_edges, dtype=np.int64)
    phi, psi = port_maps(n, G, maps)
    NEW0 = G * N1
    N = NEW0 + 10 * n
    E = []
    # copy edges
    for c in range(G):
        E.append(base_edges + c * N1)
    # new-vertex edges
    rows_a, rows_b = [], []
    for g in range(alpha):
        pat = pattern[g]
        for kind in ('U', 'B'):
            for j in range(5):
                port, rel = label_rule(pat, kind, j)
                lam = j if kind == 'U' else 5 + j
                for k in range(n):
                    newv = NEW0 + 10 * k + lam
                    for r in rel:
                        c = 5 * g + r
                        if side == 'P':   # outer ports are points, inner ports are lines
                            base = int(phi[c][k]) if port == 'outer' else n + int(psi[c][k])
                        else:             # side 'L': outer ports are lines, inner ports are points
                            base = n + int(psi[c][k]) if port == 'outer' else int(phi[c][k])
                        rows_a.append(newv)
                        rows_b.append(c * N1 + base)
    new_edges = np.stack([np.array(rows_a, dtype=np.int64), np.array(rows_b, dtype=np.int64)], axis=1)
    allE = np.concatenate(E + [new_edges], axis=0)
    return N, allE, dict(n=n, alpha=alpha, G=G, N1=N1, NEW0=NEW0)


def write_edges(path, N, edges):
    with open(path, 'w') as f:
        f.write(f"{N}\n")
        np.savetxt(f, edges, fmt='%d')


def analyze(q, pattern, side, maps):
    import scipy.sparse as sp
    from scipy.sparse.csgraph import shortest_path
    N, E, info = build(q, pattern, side, maps)
    n, N1, NEW0, G = info['n'], info['N1'], info['NEW0'], info['G']
    a, b = E[:, 0], E[:, 1]
    A = sp.coo_matrix((np.ones(2 * len(a)), (np.r_[a, b], np.r_[b, a])), shape=(N, N)).tocsr()
    deg = np.bincount(np.r_[a, b], minlength=N)
    print(f"N={N} edges={len(a)} degree set={sorted(set(deg.tolist()))}", flush=True)
    # class of each vertex: 0 = copy point, 1 = copy line, 2 = new vertex
    cls = np.empty(N, dtype=np.int64)
    idx = np.arange(N)
    cls[:] = 2
    inside = idx < NEW0
    v = idx % N1
    cls[inside & (v < n)] = 0
    cls[inside & (v >= n)] = 1
    names = ['copy-point', 'copy-line', 'new']
    diam = 0
    best = {}  # (cls_s, cls_t) -> max distance
    count_at = {}
    ecc = np.zeros(N, dtype=np.int64)
    chunk = 400
    for s0 in range(0, N, chunk):
        srcs = np.arange(s0, min(N, s0 + chunk))
        D = shortest_path(A, method='D', directed=False, unweighted=True, indices=srcs)
        D = D.astype(np.int64)
        ecc[srcs] = D.max(axis=1)
        diam = max(diam, int(D.max()))
        for ci in range(3):
            rows = cls[srcs] == ci
            if not rows.any():
                continue
            sub = D[rows]
            for cj in range(3):
                cols = cls == cj
                m = sub[:, cols]
                if m.size == 0:
                    continue
                mx = int(m.max())
                key = (names[ci], names[cj])
                cur = best.get(key, -1)
                cnt = int((m == mx).sum())
                if mx > cur:
                    best[key], count_at[key] = mx, cnt
                elif mx == cur:
                    count_at[key] += cnt
    print(f"diameter = {diam}")
    print("per class pair: max distance (ordered pairs at max distance counted over all sources)")
    for key in sorted(best):
        print(f"  {key[0]:>10s} -> {key[1]:<10s}: max {best[key]}  (pairs at that max, within this class pair: {count_at[key]})")
    ecc_max = ecc.max()
    print(f"eccentricity max = {ecc_max}; sources with ecc = diameter by class:",
          {names[c]: int(((ecc == diam) & (cls == c)).sum()) for c in range(3)})
    return N, E, info, D, ecc


if __name__ == '__main__':
    cmd = sys.argv[1]
    q = int(sys.argv[2])
    pattern, side, maps = sys.argv[3], sys.argv[4], sys.argv[5]
    if cmd == 'build':
        out = sys.argv[6]
        N, E, info = build(q, pattern, side, maps)
        write_edges(out, N, E)
        print(f"wrote {out}: N={N} edges={len(E)} info={info}")
    elif cmd == 'analyze':
        analyze(q, pattern, side, maps)
    else:
        raise SystemExit(__doc__)
