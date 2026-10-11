import itertools
import random
import time
from collections import deque

import lib


def _gq_lines(q):
    """Points and totally isotropic lines of the symplectic quadrangle W(q), a GQ of order (q, q)."""
    F = lib.GF(q)

    def normalize(v):
        for c in v:
            if c:
                inv = F.inv(c)
                return tuple(F.mul(x, inv) for x in v)
        return None

    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and normalize(v) == v]
    index = {p: i for i, p in enumerate(pts)}

    def form(x, y):
        a = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        b = F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2]))
        return F.add(a, b)

    npts = len(pts)
    done = set()          # point pairs (i < j) already covered by a built line
    lines = []
    for i in range(npts):
        p = pts[i]
        for j in range(i + 1, npts):
            if (i, j) in done or form(p, pts[j]) != 0:
                continue
            r = pts[j]
            members = {i}
            for a in range(q):
                v = tuple(F.add(r[k], F.mul(a, p[k])) for k in range(4))
                members.add(index[normalize(v)])
            mem = sorted(members)              # q+1 points spanning <p, r>
            for x in range(len(mem)):
                for y in range(x + 1, len(mem)):
                    done.add((mem[x], mem[y]))
            lines.append(mem)
    return pts, lines


def _gq_base(q):
    """Incidence graph of W(q): points 0..m-1, lines m..2m-1. Returns (m, incidence sets, edges)."""
    pts, lines = _gq_lines(q)
    m = len(pts)
    if len(lines) != m:
        return None
    inc = [set() for _ in range(m)]
    edges = []
    for li, L in enumerate(lines):
        for p in L:
            inc[p].add(li)
            edges.append((p, m + li))
    return m, inc, edges


def _augment(p0, comp, match_pt, match_line):
    """BFS for an augmenting path from free point p0 in the complement graph; apply it if found."""
    parent = {}
    seen_pts = {p0}
    queue = deque([p0])
    while queue:
        p = queue.popleft()
        for l in comp[p]:
            if l in parent:
                continue
            parent[l] = p
            if match_line[l] == -1:
                cur = l
                while True:
                    pp = parent[cur]
                    prev = match_pt[pp]
                    match_pt[pp] = cur
                    match_line[cur] = pp
                    if pp == p0:
                        return True
                    cur = prev
            q = match_line[l]
            if q not in seen_pts:
                seen_pts.add(q)
                queue.append(q)
    return False


def _complement_matching(m, inc, rng):
    """Perfect matching between points and lines using only NON-incident pairs (or None)."""
    comp = []
    for p in range(m):
        c = [l for l in range(m) if l not in inc[p]]
        rng.shuffle(c)
        comp.append(c)
    match_pt = [-1] * m
    match_line = [-1] * m
    for p in range(m):                      # greedy start
        for l in comp[p]:
            if match_line[l] == -1:
                match_line[l] = p
                match_pt[p] = l
                break
    for p0 in range(m):                     # complete with augmenting paths
        if match_pt[p0] == -1 and not _augment(p0, comp, match_pt, match_line):
            return None
    return match_pt


def _gq_construct(q, extra, rng):
    """GQ(q,q) incidence graph; if extra, add a perfect non-incidence matching (degree q+2)."""
    res = _gq_base(q)
    if res is None:
        return None
    m, inc, edges = res
    if extra:
        mt = _complement_matching(m, inc, rng)
        if mt is None:
            return None
        edges = edges + [(p, m + mt[p]) for p in range(m)]
    return 2 * m, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    rng = random.Random(seed)
    if D == 4:
        # Prefer GQ(d-1, d-1) incidence (degree d); otherwise GQ(d-2, d-2) plus a matching (degree d).
        for q, extra in ((d - 1, False), (d - 2, True)):
            if q < 2 or not lib.is_prime_power(q):
                continue
            got = _gq_construct(q, extra, rng)
            if got is not None and lib.is_valid(got[0], got[1], d, D):
                return got
    # Fallback: Haar-graph search (parent method).
    best = lib.haar_graph(d, range(d))          # K_{d,d}: always valid
    m, misses = d + 1, 0
    while time.monotonic() < deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            best, misses = found, 0
        else:
            misses += 1
        m += 1
    return best
