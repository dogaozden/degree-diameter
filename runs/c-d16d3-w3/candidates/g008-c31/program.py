"""Combined program. For D = 3 it adds a different construction: cyclic Haar graphs H(Z_m, S) with |S| = d.
H(Z_m, S) is bipartite, d-regular, and has diameter 3 exactly when S - S = Z_m (a difference cover). The C
engine searches for the largest m with a difference cover of size d by annealing. The arc-extended
projective-plane candidates and the parent's C grow-by-two search remain as fallbacks, and every result is
checked with lib.is_valid."""
import itertools
import random
import time

import lib

# ----------------------------------------------------------------------------
# C engine 1: difference-cover search for cyclic Haar graphs (diameter 3).
# Output is the Haar graph H(Z_m, S) with the largest m found, or "0 0".
# ----------------------------------------------------------------------------

C_COVER = r'''
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXK 64
#define MAXM 4096

static uint64_t rs = 0x2545F4914F6CDD1DULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static int K, M;
static int S[MAXK];
static int cnt[MAXM];
static int uncovered;   /* number of residues r in 1..M-1 with cnt[r] == 0 */

static int md(int x) { x %= M; return x < 0 ? x + M : x; }
static void inc_r(int r) { if (cnt[r] == 0) uncovered--; cnt[r]++; }
static void dec_r(int r) { cnt[r]--; if (cnt[r] == 0) uncovered++; }

static int in_set(int y, int skip) {
    for (int j = 0; j < K; j++)
        if (j != skip && S[j] == y) return 1;
    return 0;
}

static int in_prefix(int y, int n) {
    for (int j = 0; j < n; j++)
        if (S[j] == y) return 1;
    return 0;
}

static void rebuild(void) {
    memset(cnt, 0, sizeof(int) * (size_t)M);
    uncovered = M - 1;
    for (int i = 0; i < K; i++)
        for (int j = i + 1; j < K; j++) {
            inc_r(md(S[i] - S[j]));
            inc_r(md(S[j] - S[i]));
        }
}

static void replace_el(int idx, int y) {
    int x = S[idx];
    for (int j = 0; j < K; j++) {
        if (j == idx) continue;
        dec_r(md(x - S[j]));
        dec_r(md(S[j] - x));
    }
    for (int j = 0; j < K; j++) {
        if (j == idx) continue;
        inc_r(md(y - S[j]));
        inc_r(md(S[j] - y));
    }
    S[idx] = y;
}

static int attempt(long steps) {
    S[0] = 0;
    for (int i = 1; i < K; i++) {
        int y;
        do { y = rndint(M); } while (in_prefix(y, i));
        S[i] = y;
    }
    rebuild();
    for (long s = 0; s < steps; s++) {
        if (uncovered == 0) return 1;
        double T = 1.2 * pow(0.03 / 1.2, (double)s / (double)steps);
        int idx = 1 + rndint(K - 1);
        int y;
        if (rnd01() < 0.8) {
            /* Target an uncovered residue r: move S[idx] so that S[j] +- r becomes a difference. */
            int r = 1 + rndint(M - 1);
            for (int t = 0; t < M - 1 && cnt[r] != 0; t++) r = (r % (M - 1)) + 1;
            int j = rndint(K);
            y = (rnd() & 1) ? md(S[j] + r) : md(S[j] - r);
        } else {
            y = rndint(M);
        }
        if (y == S[idx] || in_set(y, idx)) continue;
        int x = S[idx];
        int old = uncovered;
        replace_el(idx, y);
        int delta = uncovered - old;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) continue;
        replace_el(idx, x);
    }
    return uncovered == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    K = atoi(argv[1]);
    int m0 = atoi(argv[2]);
    double limit = atof(argv[3]);
    rs ^= (uint64_t)atol(argv[4]) * 0x9E3779B97F4A7C15ULL + 1;
    if (!rs) rs = 1;
    for (int i = 0; i < 8; i++) rnd();
    if (K < 2 || K > MAXK) { printf("0 0\n"); return 0; }

    double tend = now() + limit * 0.92;
    int bestM = 0;
    int bestS[MAXK];
    long steps = 60000;
    for (int m = (m0 < K ? K : m0); m < MAXM / 2 && now() < tend; m++) {
        if (m > K * (K - 1) + 1) break;   /* a difference cover needs m <= k(k-1)+1 */
        M = m;
        int ok = 0;
        while (!ok && now() < tend) ok = attempt(steps);
        if (!ok) break;
        bestM = m;
        memcpy(bestS, S, sizeof(int) * K);
    }
    if (!bestM) { printf("0 0\n"); return 0; }
    printf("%d %d\n", 2 * bestM, bestM * K);
    for (int i = 0; i < bestM; i++)
        for (int a = 0; a < K; a++)
            printf("%d %d\n", i, bestM + (i + bestS[a]) % bestM);
    return 0;
}
'''

# ----------------------------------------------------------------------------
# C engine 2: grow a valid graph by two vertices with annealed edge swaps.
# ----------------------------------------------------------------------------

C_GROW = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 4096
#define MAXD 32
#define MAXW (MAXN / 64)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

static int has_edge(const Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static void del_half(Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) {
            g->adj[u][i] = g->adj[u][--g->deg[u]];
            return;
        }
}

static void del_edge(Graph *g, int u, int v) {
    del_half(g, u, v);
    del_half(g, v, u);
}

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
    }
}

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int i = 0; i < g->deg[v]; i++) {
                const uint64_t *s = cur + (size_t)g->adj[v][i] * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
        badv[v] = n - c;
        total += n - c;
    }
    return total / 2;
}

static int is_valid(const Graph *g) {
    if (g->n <= 0 || g->n > MAXN) return 0;
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= g->n || u == v || g->side[u] == g->side[v]) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
        }
    }
    return bad_pairs(g) == 0;
}

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            g->deg[u] >= MAXD || g->deg[v] >= MAXD) { g->n = 0; return; }
        add_edge(g, u, v);
    }
    static int queue[MAXN];
    for (int s = 0; s < n; s++) {
        if (g->side[s] != 255) continue;
        int head = 0, tail = 0;
        g->side[s] = 0;
        queue[tail++] = s;
        while (head < tail) {
            int v = queue[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (g->side[u] == 255) { g->side[u] = 1 - g->side[v]; queue[tail++] = u; }
                else if (g->side[u] == g->side[v]) { g->n = 0; return; }
            }
        }
    }
    if (!is_valid(g)) g->n = 0;
}

static void print_graph(const Graph *g) {
    long m = 0;
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) m++;
    printf("%d %ld\n", g->n, m);
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) printf("%d %d\n", u, g->adj[u][i]);
}

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

static int grow_once(const Graph *best, Graph *work, double until) {
    int n = best->n;
    if (n + 2 > moore_bound() || n + 2 > MAXN) return 0;
    copy_graph(work, best);
    int x = n, y = n + 1;
    work->n = n + 2;
    work->deg[x] = work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_edge(work, x, y);
    static int used[MAXN];
    static int stamp = 0;
    stamp++;
    used[x] = used[y] = stamp;
    for (int k = 0, tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (work->side[a] != 0 || used[a] == stamp || work->deg[a] == 0) continue;
        int b = work->adj[a][rndint(work->deg[a])];
        if (used[b] == stamp || b >= n) continue;
        del_edge(work, a, b);
        add_edge(work, x, b);
        add_edge(work, y, a);
        used[a] = used[b] = stamp;
        k++;
    }
    long bad = bad_pairs(work);
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        int v = rndint(work->n);
        for (int tries = 0; tries < 30 && badv[v] == 0; tries++) v = rndint(work->n);
        if (work->deg[v] == 0) continue;
        int u = work->adj[v][rndint(work->deg[v])];
        int s = rndint(work->n);
        if (work->side[s] != work->side[v] || s == v || work->deg[s] == 0) continue;
        int t = work->adj[s][rndint(work->deg[s])];
        if (t == u || has_edge(work, v, t) || has_edge(work, s, u)) continue;
        del_edge(work, v, u);
        del_edge(work, s, t);
        add_edge(work, v, t);
        add_edge(work, s, u);
        long nb = bad_pairs(work);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            del_edge(work, v, t);
            del_edge(work, s, u);
            add_edge(work, v, u);
            add_edge(work, s, t);
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return is_valid(work);
}

static void grow_search(Graph *best, double until) {
    static Graph work;
    while (now() < until && best->n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice)) copy_graph(best, &work);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (D >= 2 && best.n < moore_bound()) grow_search(&best, t_end);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Projective-plane arc extensions (diameter 3), from the parent program.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index


def _loads_ok(S, s, m, nbr):
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < s for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E, list(range(2 * m, 2 * m + na)), list(range(2 * m + na, n))


def _fill_ab(n, edges, d, A, B):
    deg = [0] * n
    have = set()
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        have.add((u, v) if u < v else (v, u))
    E = list(edges)
    for a in A:
        for b in B:
            if deg[a] >= d:
                break
            if deg[b] >= d:
                continue
            key = (a, b) if a < b else (b, a)
            if key in have:
                continue
            have.add(key)
            deg[a] += 1
            deg[b] += 1
            E.append(key)
    return n, E


def _arc_candidates(d, deadline, rng):
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 1:
            continue
        m, edges, point_lines, line_points, index = _pg_data(q)
        SA = _greedy_side(m, s, point_lines, rng, 30, deadline)
        SB = _greedy_side(m, s, line_points, rng, 30, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs
        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        n_c, e_c, A, B = _arc_graph(m, edges, point_lines, line_points, SA, SB)
        out.append(_fill_ab(n_c, e_c, d, A, B))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) (diameter 4), used only for D >= 4.
# ----------------------------------------------------------------------------

def _gq_w(q):
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
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def known_start(d, D):
    """Best closed-form graph for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    def elapsed():
        return time.monotonic() - t0

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = (cand[0], cand[1])

    if D >= 3:
        consider(known_start(d, D))
        rng = random.Random(seed * 7919 + d)
        for cand in sorted(_arc_candidates(d, t0 + 0.12 * time_limit, rng), key=lambda t: -t[0]):
            consider(cand)

    if D >= 4 and elapsed() < 0.2 * time_limit:
        consider(_best_gq(d))

    # New bold branch for D = 3: cyclic Haar graphs from difference covers of size d.
    if D == 3 and best[0] < lib.moore_bound(d, D):
        budget = 0.45 * time_limit - elapsed() - 1.0
        if budget > 0.5:
            try:
                text = lib.run_c(C_COVER, [d, d, round(budget, 2), seed],
                                 timeout=budget + 5)
                consider(lib.parse_graph_text(text))
            except (RuntimeError, ValueError):
                pass   # keep the best construction so far

    # Grow the best valid graph found so far by two vertices at a time.
    budget = 0.85 * time_limit - elapsed() - 1.0
    if budget > 0.5 and best[0] < lib.moore_bound(d, D):
        try:
            text = lib.run_c(C_GROW, [d, D, seed, round(budget, 2)],
                             stdin_graph=best, timeout=budget + 5)
            n, e = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
