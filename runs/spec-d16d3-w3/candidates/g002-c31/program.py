"""Arc-extended projective plane baseline plus a difference-cover race for D = 3.

New routine: for a group G of order N (cyclic or Z_a x| Z_b), search a set S with
|S| = d, e in S, such that S S^{-1} = G and S^{-1} S = G. The bipartite graph
a_g ~ b_{g s} (s in S) on 2N vertices is d-regular with diameter 3. The search
is simulated annealing on the number of uncovered group elements, with O(d)
incremental updates per move, and a focused move that targets an uncovered
element. Groups of several orders race round-robin, and only orders larger than
the current best are kept. Every candidate is checked with lib.is_valid before
it is returned.
"""
import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective plane baseline and arc extension (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _local_arc(m, s, point_lines, line_points, S0, rng, deadline):
    """Iterated local search for a large S with all loads <= s, starting from feasible S0."""
    cl = [0] * m
    cp = [0] * m
    inS = [False] * m
    S = []

    def add(P):
        inS[P] = True
        S.append(P)
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1

    def remove(P):
        inS[P] = False
        S.remove(P)
        for L in point_lines[P]:
            cl[L] -= 1
        for Q in line_points[P]:
            cp[Q] -= 1

    def blockers(P):
        satL = {L for L in point_lines[P] if cl[L] >= s}
        satQ = {Q for Q in line_points[P] if cp[Q] >= s}
        if not satL and not satQ:
            return []
        return [R for R in S
                if any(L in satL for L in point_lines[R])
                or any(Q in satQ for Q in line_points[R])]

    for P in S0:
        add(P)
    best = list(S)
    it = 0
    while True:
        it += 1
        if (it & 255) == 0 and time.monotonic() > deadline:
            break
        P = rng.randrange(m)
        if inS[P]:
            continue
        B = blockers(P)
        if not B:
            add(P)
        elif len(B) == 1 or (len(B) == 2 and rng.random() < 0.1):
            for R in B:
                remove(R)
            add(P)
        else:
            continue
        if len(S) > len(best):
            best = list(S)
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng, threshold):
    """Return (n, edges) candidates for prime powers q with q + 1 <= d and spare s = d - q - 1 >= 1."""
    qs = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        s = d - q - 1
        if s < 1:
            continue
        m = q * q + q + 1
        kmax = s * m // (q + 1)
        if 2 * m + 2 * kmax <= threshold:
            continue
        qs.append((q, s))

    out = []
    for idx, (q, s) in enumerate(qs):
        now = time.monotonic()
        if now > deadline:
            break
        share = (deadline - now) / (len(qs) - idx)
        q_deadline = now + share
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = [_greedy_arc(m, s, point_lines, line_points, rng, 40, now + 0.3 * share)]
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S0 = max(cands, key=len, default=[])
        if not _loads_ok(S0, s, m, point_lines, line_points):
            S0 = []
        S = _local_arc(m, s, point_lines, line_points, S0, rng, q_deadline)
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Difference-cover race (diameter 3, bipartite).
#
# For a group G of order N, pick S with |S| = d and e in S (right translation
# preserves the conditions, so e may be fixed in S). Graph: a_g ~ b_{g s}.
#   a-a distance <= 2 needs S S^{-1} = G;  b-b distance <= 2 needs S^{-1} S = G;
#   a-b distance <= 3 then follows from S S^{-1} = G.
# So the graph has diameter 3 whenever both covers are full. Order 2N, degree d.
# ----------------------------------------------------------------------------

def _make_group(a, b, r):
    """Group Z_a x|_r Z_b (element (x, y) coded as x*b + y), with mult table M and inverse table I."""
    N = a * b
    rp = [pow(r, y, a) for y in range(b)]
    M = [None] * N
    for x1 in range(a):
        for y1 in range(b):
            g1 = x1 * b + y1
            row = [0] * N
            rr = rp[y1]
            for x2 in range(a):
                cx = (x1 + rr * x2) % a
                off = x2 * b
                for y2 in range(b):
                    row[off + y2] = cx * b + (y1 + y2) % b
            M[g1] = row
    I = [0] * N
    for x in range(a):
        for y in range(b):
            ny = (-y) % b
            nx = (-pow(r, ny, a) * x) % a
            I[x * b + y] = nx * b + ny
    return N, M, I


def _cover_reset(st, d, rng):
    """Random S containing the identity 0, with fresh coverage counts."""
    N, M, I = st['N'], st['M'], st['I']
    S = [0] + rng.sample(range(1, N), d - 1)
    c1 = [0] * N
    c2 = [0] * N
    for s in S:
        for t in S:
            c1[M[s][I[t]]] += 1
            c2[M[I[s]][t]] += 1
    st['S'] = S
    st['c1'] = c1
    st['c2'] = c2
    st['unc'] = sum(1 for c in c1 if c == 0) + sum(1 for c in c2 if c == 0)
    st['steps'] = 0


def _cover_chunk(st, steps, rng, d):
    """Simulated annealing on the number of uncovered elements (both covers), with focused moves."""
    M, I, N = st['M'], st['I'], st['N']
    S, cov1, cov2, T = st['S'], st['c1'], st['c2'], st['T']
    unc = st['unc']
    exp = math.exp
    done = 0
    for _ in range(steps):
        done += 1
        if unc == 0:
            break
        i = rng.randrange(1, d)
        o = S[i]
        x = -1
        if rng.random() < 0.7:
            if rng.random() < 0.5:
                cov = cov1
                h = -1
                for _try in range(30):
                    c = rng.randrange(N)
                    if cov[c] == 0:
                        h = c
                        break
                if h >= 0:
                    x = M[h][S[rng.randrange(d)]]      # x * t^{-1} = h
            else:
                cov = cov2
                h = -1
                for _try in range(30):
                    c = rng.randrange(N)
                    if cov[c] == 0:
                        h = c
                        break
                if h >= 0:
                    x = M[S[rng.randrange(d)]][h]      # s^{-1} * x = h
        if x < 0:
            x = rng.randrange(1, N)
        if x == 0 or x == o or x in S:
            continue

        Io = I[o]
        Ix = I[x]
        rem1 = [0]
        rem2 = [0]
        add1 = [0]
        add2 = [0]
        for j in range(d):
            if j == i:
                continue
            t = S[j]
            It = I[t]
            rem1.append(M[o][It])
            rem1.append(M[t][Io])
            rem2.append(M[Io][t])
            rem2.append(M[It][o])
            add1.append(M[x][It])
            add1.append(M[t][Ix])
            add2.append(M[Ix][t])
            add2.append(M[It][x])

        delta = 0
        for g in rem1:
            cov1[g] -= 1
            if cov1[g] == 0:
                delta += 1
        for g in rem2:
            cov2[g] -= 1
            if cov2[g] == 0:
                delta += 1
        for g in add1:
            if cov1[g] == 0:
                delta -= 1
            cov1[g] += 1
        for g in add2:
            if cov2[g] == 0:
                delta -= 1
            cov2[g] += 1

        if delta <= 0 or rng.random() < exp(-delta / T):
            S[i] = x
            unc += delta
        else:
            for g in add1:
                cov1[g] -= 1
            for g in add2:
                cov2[g] -= 1
            for g in rem1:
                cov1[g] += 1
            for g in rem2:
                cov2[g] += 1
    st['unc'] = unc
    st['steps'] += done


def _specs(lo, hi, d, rng, cap):
    """Group specs (a, b, r) with order N = a*b in [lo, hi]; includes cyclic and semidirect groups."""
    out = []
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        out.append((N, 1, 1))
        for b in range(2, N):
            if N % b:
                continue
            a = N // b
            if a < 2:
                continue
            rs = [r for r in range(2, a)
                  if math.gcd(r, a) == 1 and pow(r, b, a) == 1 % a]
            if rs:
                out.append((a, b, rs[rng.randrange(len(rs))]))
            out.append((a, b, 1))
    if len(out) > cap:
        rng.shuffle(out)
        out = out[:cap]
    return out


def _race(d, specs, lo, rng, deadline):
    """Round-robin the groups; a success at order N only lets groups of larger order continue."""
    states = [{'a': a, 'b': b, 'r': r, 'N': a * b, 'M': None} for a, b, r in specs]
    best = None
    best_N = lo - 1
    while time.monotonic() < deadline:
        if all(st['N'] <= best_N for st in states):
            break
        for st in states:
            if time.monotonic() >= deadline:
                break
            if st['N'] <= best_N:
                continue
            if st['M'] is None:
                _, M, I = _make_group(st['a'], st['b'], st['r'])
                st['M'], st['I'] = M, I
                st['T'] = rng.choice((0.3, 0.45))
                _cover_reset(st, d, rng)
            _cover_chunk(st, 2000, rng, d)
            if st['unc'] == 0:
                best_N = st['N']
                best = (st['N'], st['M'], list(st['S']))
            elif st['steps'] > 60000:
                _cover_reset(st, d, rng)
    return best


def _graph_from(N, M, S):
    """Bipartite graph a_g ~ b_{g s} on 2N vertices: a_g = g, b_h = N + h."""
    edges = []
    for g in range(N):
        row = M[g]
        for s in S:
            edges.append((g, N + row[s]))
    return 2 * N, edges


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = 0.8 * time_limit
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

        try:
            arcs = _arc_extensions(d, start + 0.15 * budget,
                                   random.Random(seed * 7919 + d), best_n)
            for n_c, e_c in arcs:
                consider(n_c, e_c)
        except Exception:
            pass

        if D == 3:
            try:
                lo = best_n // 2 + 1
                hi = d * d - d + 1   # Moore bound on |G| for diameter 3
                if lo <= hi:
                    specs = _specs(lo, hi, d, rng, 30)
                    res = _race(d, specs, lo, rng, deadline)
                    if res is not None:
                        N, M, S = res
                        n, e = _graph_from(N, M, S)
                        consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
