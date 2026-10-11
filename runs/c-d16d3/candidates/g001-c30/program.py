import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: greedy spare-capacity vertex insertion with ball set cover.
#
# Given a valid bipartite graph, repeatedly try to add a new vertex x on one
# side. x is joined to a set T of opposite-side vertices that still have spare
# degree. If the radius-(D-1) balls of T cover every existing vertex, then every
# vertex is within distance D of x. Adding x and its edges only shortens
# distances, so the old diameter bound still holds and the graph stays valid.
# The set T is chosen by randomized greedy max-coverage. Each success recomputes
# the balls. The search runs until the time budget ends and prints the result.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXV 4096
#define WORDS ((MAXV + 63) / 64)
#define MAXD 256

static int d, D, R, N;
static int deg[MAXV];
static int col[MAXV];
static int *adj;
static uint64_t ball[MAXV][WORDS];
static uint64_t cov[WORDS];
static int mark[MAXV];
static int stamp = 0;
static int qbuf[MAXV];
static char used[MAXV];
static int chosen[MAXD];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void compute_balls(void) {
    for (int v = 0; v < N; v++) {
        uint64_t *b = ball[v];
        int head = 0, tail = 0, layer_end;
        memset(b, 0, sizeof(uint64_t) * WORDS);
        stamp++;
        mark[v] = stamp;
        qbuf[tail++] = v;
        layer_end = tail;
        for (int r = 0; r < R; r++) {
            while (head < layer_end) {
                int u = qbuf[head++];
                for (int i = 0; i < deg[u]; i++) {
                    int w = adj[(size_t)u * d + i];
                    if (mark[w] != stamp) {
                        mark[w] = stamp;
                        qbuf[tail++] = w;
                    }
                }
            }
            layer_end = tail;
            if (head == tail) break;
        }
        for (int i = 0; i < tail; i++) {
            int u = qbuf[i];
            b[u >> 6] |= 1ULL << (u & 63);
        }
    }
}

static int try_insert(int c, int firstrand) {
    int nw = (N + 63) / 64;
    int nch = 0;
    for (int w = 0; w < nw; w++) cov[w] = 0;
    memset(used, 0, (size_t)N);
    int covered = 0;
    while (nch < d && covered < N) {
        int pick = -1, bg = 0, nties = 0, nposs = 0;
        for (int v = 0; v < N; v++) {
            if (col[v] == c || deg[v] >= d || used[v]) continue;
            int g = 0;
            for (int w = 0; w < nw; w++) g += pc64(ball[v][w] & ~cov[w]);
            if (g <= 0) continue;
            if (firstrand && nch == 0) {
                nposs++;
                if (rnd() % (uint64_t)nposs == 0) pick = v;
            } else if (g > bg) {
                bg = g;
                pick = v;
                nties = 1;
            } else if (g == bg) {
                nties++;
                if (rnd() % (uint64_t)nties == 0) pick = v;
            }
        }
        if (pick < 0) break;
        used[pick] = 1;
        chosen[nch++] = pick;
        covered = 0;
        for (int w = 0; w < nw; w++) {
            cov[w] |= ball[pick][w];
            covered += pc64(cov[w]);
        }
    }
    if (covered < N || nch == 0 || N + 1 >= MAXV) return 0;
    int x = N;
    col[x] = c;
    deg[x] = 0;
    for (int i = 0; i < nch; i++) {
        int t = chosen[i];
        adj[(size_t)x * d + deg[x]++] = t;
        adj[(size_t)t * d + deg[t]++] = x;
    }
    N++;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double limit = atof(argv[4]);
    rs ^= (seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (d < 1 || d > MAXD || D < 2 || n0 < 0 || n0 > MAXV - 512 || m0 < 0) {
        printf("0 0\n");
        return 0;
    }
    R = D - 1;
    adj = malloc(sizeof(int) * (size_t)MAXV * d);
    N = n0;
    for (int v = 0; v < MAXV; v++) deg[v] = 0;
    int bad = 0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { bad = 1; break; }
        if (u < 0 || v < 0 || u >= N || v >= N || u == v || deg[u] >= d || deg[v] >= d) {
            bad = 1;
            break;
        }
        adj[(size_t)u * d + deg[u]++] = v;
        adj[(size_t)v * d + deg[v]++] = u;
    }
    if (bad) {
        printf("0 0\n");
        return 0;
    }

    /* 2-colour the start graph. */
    for (int v = 0; v < N; v++) col[v] = -1;
    int bip = 1;
    for (int s = 0; s < N && bip; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int h = 0, t = 0;
        qbuf[t++] = s;
        while (h < t && bip) {
            int u = qbuf[h++];
            for (int i = 0; i < deg[u]; i++) {
                int w = adj[(size_t)u * d + i];
                if (col[w] < 0) {
                    col[w] = 1 - col[u];
                    qbuf[t++] = w;
                } else if (col[w] == col[u]) {
                    bip = 0;
                }
            }
        }
    }

    if (bip && N > 0) {
        clock_t t0 = clock();
        compute_balls();
        long long it = 0;
        while (1) {
            if ((it & 31) == 0) {
                double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
                if (el >= limit) break;
            }
            it++;
            if (N >= MAXV - 1) break;
            int c = (int)(rnd() & 1ULL);
            int fr = (rnd() % 3 == 0);
            if (try_insert(c, fr)) {
                compute_balls();
            }
        }
    }

    long long M = 0;
    for (int v = 0; v < N; v++) M += deg[v];
    M /= 2;
    printf("%d %lld\n", N, M);
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < deg[v]; i++) {
            int w = adj[(size_t)v * d + i];
            if (w > v) printf("%d %d\n", v, w);
        }
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Every old vertex has degree q+1,
# so with d >= q+1 it has spare capacity s = d - q - 1. Choose a point set S
# with every line holding <= s points of S. For each P in S add a new A-vertex
# joined to the q+1 lines through P; for each j in S add a new B-vertex joined
# to the q+1 points on line j. Diameter stays 3.
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
    """Build the extended graph: old PG incidence plus a new A and a new B vertex per element of S."""
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


# ----------------------------------------------------------------------------
# C augmentation step (spare-capacity insertion), run on the best graph found.
# ----------------------------------------------------------------------------

def _augment(n, edges, d, D, seed, seconds):
    """Run the C insertion engine on (n, edges) for about `seconds`; return (n, edges) or None."""
    if seconds < 1.0 or n < 1:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(seconds, 2)],
                        stdin_graph=(n, edges), timeout=seconds + 15.0)
        return lib.parse_graph_text(out)
    except (RuntimeError, ValueError):
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

    # Arc-extended projective plane graphs: diameter 3, valid for all D >= 3.
    if D >= 3:
        cands = _arc_extensions(d, start + 0.15 * time_limit, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            consider(n_c, e_c)

    if D >= 4 and time.monotonic() < start + 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Annealed group voltage lifts, only for D >= 4 (they rarely beat the D = 3 arc graphs).
    if D >= 4:
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        lift_deadline = start + 0.4 * time_limit
        while time.monotonic() < lift_deadline:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, lift_deadline, iters=400)
            if res is not None:
                consider(res[0], res[1])

    # Spend the rest of the budget in C: insert new vertices into spare capacity.
    end = start + 0.85 * time_limit
    budget = end - time.monotonic() - 2.0
    aug = _augment(best_n, best[1], d, D, seed, budget)
    if aug is not None:
        consider(aug[0], aug[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
