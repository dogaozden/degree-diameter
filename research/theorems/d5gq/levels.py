"""Level graphs over a GQ of order (s,s), surgery and hubs (Definitions 2.1 and 3.1 of D5_QUADRANGLE.md), written out
as an edge list for apsp.c.  Elements of a level: points 0..np-1 and lines np..np+nl-1 (an "element id").

types: list of 'H'/'D' (length 2r+1).  A(H) = points, B(H) = lines, A(D) = lines, B(D) = points.
M[(j,k)]: dict or array  A-element (point id or line id, *without* the np offset) -> B-element of level j+k.
R[(j,k)]: set of freed A-elements.
Bhubs: list of lists [(j, a, (j,k)), ...] one slot per level: B-hub joined to A-element a of level j, freed on (j,k).
Ahubs: list of lists [(j, b, (i,k)), ...]: A-hub joined to B-element b of level j, where b = M[(i,k)](a), a in R[(i,k)].
Y: list of (Bhub index, Ahub index) edges.
"""
import numpy as np
import random, subprocess, os

HERE = os.path.dirname(os.path.abspath(__file__))


def Aset(G, tau):
    return 'P' if tau == 'H' else 'L'


def eid(G, kind, i):
    return i if kind == 'P' else G.np + i


def rotational_arcs(n_lev):
    r = (n_lev - 1) // 2
    return [(j, (j + k) % n_lev) for j in range(n_lev) for k in range(1, r + 1)]


def build(G, types, M, R=None, Bhubs=(), Ahubs=(), Y=(), check_slots=True, arcs=None):
    """Transitions are keyed by arcs (u, v) of a regular tournament on the levels (default: rotational, u -> u+k).
    For backward compatibility a key (j, k) with arcs=None means the arc (j, j+k)."""
    n_lev = len(types); r = (n_lev - 1) // 2
    per = G.np + G.nl
    if arcs is None:
        keymap = {(j, k): (j, (j + k) % n_lev) for j in range(n_lev) for k in range(1, r + 1)}
    else:
        keymap = {a: a for a in arcs}
    edges = []
    for j in range(n_lev):
        base = j * per
        for l, pts in enumerate(G.lines):
            for p in pts:
                edges.append((base + p, base + G.np + l))
    R = R or {}
    freed_slots = {}
    for t, (j, j2) in keymap.items():
        if True:
            ka = Aset(G, types[j]); kb = 'L' if types[j2] == 'H' else 'P'
            Mt = M[t]; Rt = R.get(t, ())
            size = G.np if ka == 'P' else G.nl
            img = set()
            for a in range(size):
                b = Mt[a]
                img.add(b)
                if a in Rt:
                    continue
                edges.append((j * per + eid(G, ka, a), j2 * per + eid(G, kb, b)))
            assert len(img) == size, 'matching %s not a bijection' % (t,)
    nv = n_lev * per
    used = set()
    for h, slots in enumerate(Bhubs):
        hv = nv + h
        levs = sorted(s[0] for s in slots)
        assert levs == list(range(n_lev)), 'B-hub %d must have one slot per level' % h
        for (j, a, t) in slots:
            if check_slots:
                assert keymap[t][0] == j and a in R.get(t, ()), (h, j, a, t)
                key = ('A', t, a); assert key not in used, key; used.add(key)
            ka = Aset(G, types[j])
            edges.append((hv, j * per + eid(G, ka, a)))
    nB = len(Bhubs)
    for g, slots in enumerate(Ahubs):
        gv = nv + nB + g
        levs = sorted(s[0] for s in slots)
        assert levs == list(range(n_lev)), 'A-hub %d must have one slot per level' % g
        for (j, b, t) in slots:
            kb = 'L' if types[j] == 'H' else 'P'
            if check_slots:
                assert keymap[t][1] == j
                a = [x for x in R.get(t, ()) if M[t][x] == b]
                assert a, (g, j, b, t)
                key = ('B', t, a[0]); assert key not in used, key; used.add(key)
            edges.append((gv, j * per + eid(G, kb, b)))
    for (h, g) in Y:
        edges.append((nv + h, nv + nB + g))
    n = nv + nB + len(Ahubs)
    return n, edges


def write_edges(path, n, edges):
    with open(path, 'w') as f:
        f.write('%d\n' % n)
        for a, b in edges:
            f.write('%d %d\n' % (a, b))


def apsp(path, d, D, threads=1):
    exe = os.path.join(HERE, 'apsp_mt' if threads > 1 else 'apsp')
    args = [exe, path, str(d), str(D)] + ([str(threads)] if threads > 1 else [])
    out = subprocess.run(args, capture_output=True, text=True).stdout
    return out.strip()


def random_bijection(n, rng):
    p = list(range(n)); rng.shuffle(p); return p


def identity(n):
    return list(range(n))


def repaired_two_levels(G, ka, M, R):
    """Exact two-level test (Theorem E) of a transition whose source A-type is ka ('P' or 'L') and matching M
    (A-elements -> B-elements of the target, which have the *other* type when the transition is non-friendly...).
    Here M maps source A-elements to target B-elements; target B-type = 'L' if non-friendly H->H else 'P' etc.
    We test with explicit distances: pair (u, j), (v, j') is fine iff exists a not in R with d(u,a) + d(M a, v) <= 4.
    Returns the number of bad ordered pairs (u in level j, v in level j')."""
    raise NotImplementedError
