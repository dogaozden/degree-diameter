import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine for D = 3: simulated annealing over difference covers.
#
# A k-subset S of Z_m whose nonzero differences cover Z_m \ {0} gives the
# Haar graph H(m, S) (2m vertices, k-regular, diameter 3). The C search uses
# targeted moves: pick an uncovered residue x and replace some element by
# S_j +- x, which covers x immediately. Otherwise it makes random moves.
# Incremental difference counts make each move O(k). The engine increases m
# while covers are found and prints the Haar graph as "n m" plus edges.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 256
#define MAXM 65536

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static uint32_t rndu(uint32_t n) { return (uint32_t)(rnd64() % n); }
static double rndf(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int K, M;
static int S[MAXK];
static int cnt[MAXM];
static unsigned char inS[MAXM];
static int uncov;

static inline int md(int a) {
    a %= M;
    if (a < 0) a += M;
    return a;
}

/* cnt[x] = number of ordered pairs (i != j) with S_i - S_j = x (mod M). */
static void counts_init(void) {
    int i, j;
    memset(cnt, 0, sizeof(int) * (size_t)M);
    for (i = 0; i < K; i++)
        for (j = 0; j < K; j++)
            if (i != j) cnt[md(S[i] - S[j])]++;
    uncov = 0;
    for (i = 1; i < M; i++)
        if (cnt[i] == 0) uncov++;
}

/* Replace S[i] by y (y not in S) and update counts and uncov. */
static void set_elem(int i, int y) {
    int old = S[i], j, a, b, t;
    for (j = 0; j < K; j++) {
        if (j == i) continue;
        t = S[j];
        a = md(old - t);
        b = md(t - old);
        if (--cnt[a] == 0) uncov++;
        if (--cnt[b] == 0) uncov++;
    }
    inS[old] = 0;
    S[i] = y;
    inS[y] = 1;
    for (j = 0; j < K; j++) {
        if (j == i) continue;
        t = S[j];
        a = md(y - t);
        b = md(t - y);
        if (cnt[a]++ == 0) uncov--;
        if (cnt[b]++ == 0) uncov--;
    }
}

/* Try to find a k-subset of Z_m covering all nonzero residues before the deadline. */
static int find_cover(int m, double deadline, int *out) {
    const int steps = 300000;
    M = m;
    while (now_s() < deadline) {
        int c, s;
        memset(inS, 0, sizeof inS);
        for (c = 0; c < K;) {
            int y = (int)rndu((uint32_t)M);
            if (!inS[y]) {
                S[c++] = y;
                inS[y] = 1;
            }
        }
        counts_init();
        for (s = 0; s < steps && uncov > 0; s++) {
            double T;
            int i, j, y, old, before, delta, x = -1, start, t;
            if ((s & 1023) == 0 && now_s() > deadline) break;
            T = pow(0.05, (double)s / (double)steps);
            if (rndf() < 0.7) {
                start = 1 + (int)rndu((uint32_t)(M - 1));
                for (t = 0; t < M - 1; t++) {
                    int z = 1 + (start - 1 + t) % (M - 1);
                    if (cnt[z] == 0) {
                        x = z;
                        break;
                    }
                }
                if (x < 0) continue;
                j = (int)rndu((uint32_t)K);
                y = (rnd64() & 1ULL) ? md(S[j] + x) : md(S[j] - x);
                i = (int)rndu((uint32_t)(K - 1));
                if (i >= j) i++;
            } else {
                i = (int)rndu((uint32_t)K);
                y = (int)rndu((uint32_t)M);
            }
            if (inS[y]) continue;
            old = S[i];
            before = uncov;
            set_elem(i, y);
            delta = uncov - before;
            if (delta > 0 && rndf() >= exp(-(double)delta / T)) set_elem(i, old);
        }
        if (uncov == 0) {
            memcpy(out, S, sizeof(int) * (size_t)K);
            return 1;
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    int d, D, cap, m, bestM = 0, fails = 0, i, c;
    unsigned long long seed;
    double budget, t_end;
    int bestS[MAXK], outS[MAXK];

    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    seed = strtoull(argv[3], NULL, 10);
    budget = atof(argv[4]);
    rs = (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    for (i = 0; i < 16; i++) rnd64();
    if (D != 3 || d < 2 || d >= MAXK) {
        printf("0 0\n");
        return 0;
    }
    K = d;
    cap = K * (K - 1) + 1;
    t_end = now_s() + budget;
    m = (int)(0.80 * cap);
    if (m < K + 1) m = K + 1;

    while (m <= cap && now_s() < t_end && bestM < cap) {
        double rem = t_end - now_s();
        double sl = (bestM == 0) ? 0.2 * rem : 0.35 * rem;
        if (find_cover(m, now_s() + sl, outS)) {
            bestM = m;
            memcpy(bestS, outS, sizeof(int) * (size_t)K);
            m++;
            fails = 0;
        } else if (bestM == 0) {
            m -= 3;
            if (m < K + 1) m = K + 1;
        } else {
            fails++;
            if (fails >= 3) break;
        }
    }

    if (bestM == 0) {
        printf("0 0\n");
        return 0;
    }
    for (i = 1; i < K; i++) {
        int v = bestS[i];
        c = i - 1;
        while (c >= 0 && bestS[c] > v) {
            bestS[c + 1] = bestS[c];
            c--;
        }
        bestS[c + 1] = v;
    }
    printf("%d %d\n", 2 * bestM, K * bestM);
    for (i = 0; i < bestM; i++)
        for (c = 0; c < K; c++)
            printf("%d %d\n", i, bestM + (i + bestS[c]) % bestM);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
# ----------------------------------------------------------------------------

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


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Python difference-cover search (fallback when the C engine fails).
# ----------------------------------------------------------------------------

def _diff_counts(S, m):
    """Return (cnt, zeros): cnt[x] = #ordered pairs (s,t), s != t, with s - t = x mod m; zeros = #{x != 0 : cnt[x] = 0}."""
    cnt = [0] * m
    k = len(S)
    for i in range(k):
        for j in range(k):
            if i != j:
                cnt[(S[i] - S[j]) % m] += 1
    zeros = sum(1 for x in range(1, m) if cnt[x] == 0)
    return cnt, zeros


def _move(S, cnt, i, y, m, zeros):
    """Replace S[i] by y (y not in S), updating cnt and the zero count. Returns the new zero count."""
    k = len(S)
    old = S[i]
    for j in range(k):
        if j != i:
            t = S[j]
            a = (old - t) % m
            b = (t - old) % m
            cnt[a] -= 1
            if cnt[a] == 0:
                zeros += 1
            cnt[b] -= 1
            if cnt[b] == 0:
                zeros += 1
    S[i] = y
    for j in range(k):
        if j != i:
            t = S[j]
            a = (y - t) % m
            b = (t - y) % m
            if cnt[a] == 0:
                zeros -= 1
            cnt[a] += 1
            if cnt[b] == 0:
                zeros -= 1
            cnt[b] += 1
    return zeros


def _cover_search(k, m, deadline, rng):
    """Find a k-subset S of Z_m whose nonzero differences cover Z_m \\ {0}; return sorted S or None."""
    if k > m or k * (k - 1) + 1 < m:
        return None
    S = rng.sample(range(m), k)
    cnt, zeros = _diff_counts(S, m)
    T = 0.3
    moves = 0
    while zeros > 0:
        moves += 1
        if moves % 512 == 0 and time.monotonic() > deadline:
            return None
        if moves % 200000 == 0:
            S = rng.sample(range(m), k)
            cnt, zeros = _diff_counts(S, m)
            continue
        i = rng.randrange(k)
        y = rng.randrange(m)
        if y in S:
            continue
        old = S[i]
        z = _move(S, cnt, i, y, m, zeros)
        delta = z - zeros
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            zeros = z
        else:
            _move(S, cnt, i, old, m, z)
    return sorted(S)


def _difference_graph(d, deadline, rng):
    """Largest cyclic Haar graph H(m, S) with |S| = d found before the deadline, as (n, edges), or None."""
    k = d
    cap = k * (k - 1) + 1
    if k < 2 or cap < 3:
        return None
    best_m, best_S = 0, None
    cur = max(k + 1, int(0.8 * cap))
    fails = 0
    while time.monotonic() < deadline and cur <= cap:
        now = time.monotonic()
        slice_end = min(deadline, now + max(1.0, 0.35 * (deadline - now)))
        S = _cover_search(k, cur, slice_end, rng)
        if S is not None:
            best_m, best_S = cur, S
            cur += 1
            fails = 0
        else:
            fails += 1
            if best_S is None:
                cur = max(k + 1, cur - 3)
            elif fails >= 3:
                break
    if best_S is None:
        return None
    return lib.haar_graph(best_m, best_S)


# ----------------------------------------------------------------------------
# Greedy vertex insertion with ball-cover certificates ("_augment").
# ----------------------------------------------------------------------------

def _side_colors(n, adj):
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _ball_masks(n, adj, R):
    """Bitmask of all vertices within distance R of each vertex."""
    reach = [1 << v for v in range(n)]
    for _ in range(R):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return reach


def _augment(n, edges, d, D, rng, deadline, max_fails=60):
    """Greedily insert vertices whose neighbourhoods cover the graph within D. Returns (n, edges)."""
    if n == 0 or D < 2:
        return n, list(edges)
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = _side_colors(n, adj)
    R = D - 1
    fails = 0
    while time.monotonic() < deadline and fails < max_fails:
        balls = _ball_masks(n, adj, R)
        full = (1 << n) - 1
        added = False
        sides = [0, 1]
        rng.shuffle(sides)
        for side in sides:
            base_cand = [u for u in range(n) if color[u] == 1 - side and len(adj[u]) < d]
            if not base_cand:
                continue
            for _attempt in range(4):
                cand = base_cand[:]
                rng.shuffle(cand)
                covered = 0
                chosen = []
                pool = cand
                while covered != full and len(chosen) < d and pool:
                    best_gain, bu, bi = 0, None, -1
                    for i, u in enumerate(pool):
                        g = (balls[u] & ~covered).bit_count()
                        if g > best_gain:
                            best_gain, bu, bi = g, u, i
                    if bu is None:
                        break
                    chosen.append(bu)
                    covered |= balls[bu]
                    pool = pool[:bi] + pool[bi + 1:]
                if covered == full:
                    w = n
                    n += 1
                    adj.append(set())
                    color.append(side)
                    for u in chosen:
                        adj[u].add(w)
                        adj[w].add(u)
                    added = True
                    break
            if added:
                break
        if added:
            fails = 0
            continue
        fails += 1
        spare_a = [u for u in range(n) if len(adj[u]) < d and color[u] == 0]
        spare_b = [u for u in range(n) if len(adj[u]) < d and color[u] == 1]
        if spare_a and spare_b:
            for _ in range(20):
                u = rng.choice(spare_a)
                v = rng.choice(spare_b)
                if u != v and v not in adj[u]:
                    adj[u].add(v)
                    adj[v].add(u)
                    break
    out = [(u, v) for u in range(n) for v in adj[u] if u < v]
    return n, out


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Simulated annealing over bi-Cayley voltage lifts (used for D >= 4).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    """Permutation g -> mul(g, s) of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        # Cheap projective-plane candidates first.
        arcs = _arc_extensions(d, start + 0.05 * time_limit, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:2]:
            consider(n_c, e_c)
        # Main path: the C difference-cover annealer (uses most of the budget).
        c_ok = False
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, f"{0.70 * time_limit:.2f}"],
                             timeout=0.86 * time_limit)
            n_h, e_h = lib.parse_graph_text(text)
            c_ok = n_h > 0 and lib.is_valid(n_h, e_h, d, D)
            if c_ok:
                consider(n_h, e_h)
        except Exception:
            c_ok = False
        # If the C engine failed, use the Python difference-cover search.
        if not c_ok:
            hg = _difference_graph(d, start + 0.95 * time_limit, rng)
            if hg is not None:
                consider(hg[0], hg[1])
    else:
        if D >= 3:
            arcs = _arc_extensions(d, start + 0.10 * time_limit, random.Random(seed * 7919 + d))
            arcs.sort(key=lambda t: -t[0])
            for n_c, e_c in arcs[:3]:
                consider(n_c, e_c)
            if arcs:
                n_a, e_a = arcs[0]
                n2, e2 = _augment(n_a, e_a, d, D, rng, start + 0.30 * time_limit)
                consider(n2, e2)

        if D >= 4 and time.monotonic() < start + 0.30 * time_limit:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])

        search_end = start + 0.55 * time_limit
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < search_end:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, search_end, iters=400)
            if res is not None:
                consider(res[0], res[1])

        if D >= 2 and time.monotonic() < start + 0.85 * time_limit:
            n_f, e_f = _augment(best[0], best[1], d, D, rng, start + 0.85 * time_limit)
            consider(n_f, e_f)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
