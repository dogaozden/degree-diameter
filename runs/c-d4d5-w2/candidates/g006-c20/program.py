"""Group-lift program. Python enumerates non-cyclic and metacyclic groups of order N (affine
subgroups of AGL(1,q) with q a prime power, optionally times a cyclic factor, plus semidirect
products Z_m x| Z_k). Each group is sent to the C engine as a multiplication table, which
hill-climbs voltages for a bipartite lift with 2pN vertices. The best lift is then grown by two
with bad-pair annealing. Every stage is validated in Python and falls back to the best valid graph."""
import itertools
import math
import random
import time

import lib

C_SOURCE = r'''
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
#define MAXP 4
#define MAXG 512

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;
static int GN;
static int GT[MAXG * MAXG];

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
    double s = 0, p = 1;
    for (int i = 0; i < D; i++) { s += p; p *= (d - 1); }
    return (long)(2.0 * s);
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

/* Number of unordered pairs at distance > D; fills badv[v] = vertices at distance > D from v. */
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

/* ---------- group lifts: vertex (fibre f, element x) -> f*N + x ---------- */

static int gmul(int x, int y) { return GT[x * GN + y]; }

static int bM[MAXP][MAXP];
typedef struct { int i, j, g; } Dart;
static Dart dts[MAXD * MAXP];
static int nd;

/* Random d-regular bipartite multigraph on p + p vertices, connected. */
static void make_base(int p) {
    for (;;) {
        memset(bM, 0, sizeof bM);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
            }
            for (int i = 0; i < p; i++) bM[i][perm[i]]++;
        }
        int seen[2 * MAXP], stack[2 * MAXP], top = 0, nseen = 1;
        memset(seen, 0, sizeof seen);
        seen[0] = 1;
        stack[top++] = 0;
        while (top) {
            int v = stack[--top];
            for (int u = 0; u < 2 * p; u++) {
                if (seen[u]) continue;
                int linked = v < p ? (u >= p && bM[v][u - p]) : (u < p && bM[u][v - p]);
                if (linked) { seen[u] = 1; nseen++; stack[top++] = u; }
            }
        }
        if (nseen == 2 * p) return;
    }
}

/* Voltage for dart `skip` on block (i, j), distinct from the other darts on that block. */
static int fresh_g(int skip, int i, int j) {
    for (;;) {
        int g = rndint(GN), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dts[t].i == i && dts[t].j == j && dts[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

static void build_lift(Graph *g, int p) {
    int N = GN;
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dts[t].i * N + x, (p + dts[t].j) * N + gmul(x, dts[t].g));
}

/* Left multiplication by any group element is an automorphism, so the diameter test only needs
 * BFS from the 2p fibre representatives (element 0 of each fibre). Returns the number of
 * (representative, vertex) pairs at distance > D. */
static int dist_buf[MAXN], queue_buf[MAXN];

static long orbit_bad(const Graph *g, int p) {
    int N = GN, nv = g->n;
    long total = 0;
    for (int b = 0; b < 2 * p; b++) {
        int src = b * N;
        for (int v = 0; v < nv; v++) dist_buf[v] = -1;
        int head = 0, tail = 0;
        dist_buf[src] = 0;
        queue_buf[tail++] = src;
        while (head < tail) {
            int v = queue_buf[head++];
            if (dist_buf[v] >= D) continue;
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (dist_buf[u] < 0) {
                    dist_buf[u] = dist_buf[v] + 1;
                    queue_buf[tail++] = u;
                }
            }
        }
        total += nv - tail;
    }
    return total;
}

/* One random base multigraph, then annealing over its voltages. Returns 1 if diameter <= D. */
static int lift_try(Graph *g, int p, double until, long steps) {
    make_base(p);
    nd = 0;
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < bM[i][j]; c++) {
                dts[nd].i = i;
                dts[nd].j = j;
                dts[nd].g = 0;
                nd++;
            }
    for (int t = 0; t < nd; t++) dts[t].g = fresh_g(t, dts[t].i, dts[t].j);
    build_lift(g, p);
    long bad = orbit_bad(g, p);
    for (long s = 0; s < steps && bad > 0; s++) {
        if ((s & 31) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = dts[t].g;
        dts[t].g = fresh_g(t, dts[t].i, dts[t].j);
        build_lift(g, p);
        long nb = orbit_bad(g, p);
        if (nb <= bad || rnd01() < 0.01) bad = nb;
        else dts[t].g = old;
    }
    build_lift(g, p);
    return bad == 0;
}

static void lift_mode(Graph *best, int p, double until) {
    static Graph cand;
    while (now() < until) {
        if (!lift_try(&cand, p, until, 40000)) continue;
        if (is_valid(&cand)) {
            copy_graph(best, &cand);
            return;
        }
    }
}

/* ---------- grow by two with bad-pair annealing ---------- */

static int pick_bad_vertex(const Graph *g) {
    static int list[MAXN];
    int c = 0;
    for (int v = 0; v < g->n; v++)
        if (badv[v] > 0) list[c++] = v;
    if (c == 0) return -1;
    return list[rndint(c)];
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
        int v;
        if (rnd01() < 0.8) {
            v = pick_bad_vertex(work);
            if (v < 0) v = rndint(work->n);
        } else {
            v = rndint(work->n);
        }
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
            bad_pairs(work);
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
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed limit mode [p] < input\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int mode = atoi(argv[5]);
    int p = argc > 6 ? atoi(argv[6]) : 1;
    t_end = now() + limit;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();
    if (d < 1 || d > MAXD || D < 1) { printf("0 0\n"); return 0; }

    static Graph best;
    best.n = 0;
    if (mode == 0) {
        int N, M;
        if (scanf("%d %d", &N, &M) != 2 || N < 1 || N > MAXG || M != N * N) {
            printf("0 0\n");
            return 0;
        }
        for (int k = 0; k < M; k++) {
            int a, b;
            if (scanf("%d %d", &a, &b) != 2 || a < 0 || a >= N) { printf("0 0\n"); return 0; }
            GT[k] = a;
        }
        for (int x = 0; x < N; x++)
            if (GT[x] != x || GT[x * N] != x) { printf("0 0\n"); return 0; }
        GN = N;
        if (p < 1 || p > MAXP || N < d || 2 * p * N > MAXN || 2L * p * N > moore_bound()) {
            printf("0 0\n");
            return 0;
        }
        lift_mode(&best, p, t_end);
    } else {
        read_start(&best);
        if (best.n > 0) grow_search(&best, t_end);
    }
    if (best.n <= 0 || !is_valid(&best)) { printf("0 0\n"); return 0; }
    print_graph(&best);
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q+1, diameter 4."""
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


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates valid for diameter D (may be empty)."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_gq_w(q))
    return out


def _divisors(n):
    return [x for x in range(1, n + 1) if n % x == 0]


def _specs(N):
    """Descriptions of groups of order N: semidirect Z_m x| Z_k, and affine AGL-subgroups
    x|_{GF(q)} (times Z_kk), which include non-metacyclic groups such as 2^4:3 x 2."""
    out = []
    for k in _divisors(N):
        m = N // k
        if m == 1:
            out.append(("sd", 1, k, 0))
            continue
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
        if not rs:
            continue
        step = max(1, len(rs) // 6)
        for r in rs[::step]:
            out.append(("sd", m, k, r))
    for q in range(2, N + 1):
        if N % q or not lib.is_prime_power(q):
            continue
        rem = N // q
        for h in _divisors(q - 1):
            if rem % h == 0:
                out.append(("aff", q, h, rem // h))
    return out


def _affine_table(q, h):
    """Group {x -> a x + b : a in H}, H the subgroup of order h in GF(q)*. Identity has index 0."""
    F = lib.GF(q)
    g = F.primitive_element()
    step = (q - 1) // h
    H = [F.pow(g, step * i) for i in range(h)]
    elems = [(a, b) for a in H for b in range(q)]
    idx = {e: i for i, e in enumerate(elems)}
    N = len(elems)
    T = [[0] * N for _ in range(N)]
    for i, (a1, b1) in enumerate(elems):
        for j, (a2, b2) in enumerate(elems):
            T[i][j] = idx[(F.mul(a1, a2), F.add(F.mul(a1, b2), b1))]
    return N, T


def _times_cyclic(N, T, k):
    M = N * k
    U = [[0] * M for _ in range(M)]
    for x in range(M):
        i, c = divmod(x, k)
        row = U[x]
        for y in range(M):
            j, e = divmod(y, k)
            row[y] = T[i][j] * k + (c + e) % k
    return M, U


def _sd_table(m, k, r):
    N, mul, _ = lib.semidirect_group(m, k, r)
    return N, [[mul(x, y) for y in range(N)] for x in range(N)]


def _build_table(spec):
    if spec[0] == "sd":
        _, m, k, r = spec
        return _sd_table(m, k, r)
    _, q, h, kk = spec
    N, T = _affine_table(q, h)
    if kk > 1:
        N, T = _times_cyclic(N, T, kk)
    return N, T


def _table_graph(N, T):
    """Encode a multiplication table as the C stdin format: header "N N*N", then pairs (T[x][y], 0)."""
    return (N, [(T[x][y], 0) for x in range(N) for y in range(N)])


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    moore = lib.moore_bound(d, D)
    if d > 31 or best[0] >= moore:
        return best

    budget = 0.85 * time_limit - 3.0 - (time.monotonic() - t0)
    if budget < 2.0:
        return best

    end = time.monotonic() + budget
    lift_end = time.monotonic() + 0.6 * budget
    rng = random.Random(seed * 1000003 + 12345)
    specs_cache = {}
    tables = {}
    misses = 0

    # Phase A: group lifts. Orders N are kept just above what is needed to beat the best graph.
    while misses < 40:
        if lift_end - time.monotonic() < 1.0:
            break
        cands = []
        for p in (1, 2, 3, 4):
            lo = max(d, -(-(best[0] + 2) // (2 * p)))
            hi = min(moore // (2 * p), lo + 14, 4096 // (2 * p), 512)
            for N in range(lo, hi + 1):
                if N not in specs_cache:
                    specs_cache[N] = _specs(N)
                if specs_cache[N]:
                    cands.append((p, N))
        if not cands:
            break
        p, N = rng.choice(cands)
        spec = rng.choice(specs_cache[N])
        try:
            if spec not in tables:
                tables[spec] = _build_table(spec)
            NN, T = tables[spec]
            slice_t = min(lift_end - time.monotonic(), 4.0)
            if slice_t < 0.5:
                break
            text = lib.run_c(C_SOURCE, [d, D, rng.randrange(1, 1 << 30), slice_t, 0, p],
                             stdin_graph=_table_graph(NN, T), timeout=slice_t + 5)
            n2, e2 = lib.parse_graph_text(text)
            if n2 > best[0] and lib.is_valid(n2, e2, d, D):
                best = (n2, e2)
                misses = 0
            else:
                misses += 1
        except Exception:
            misses += 1

    # Phase B: grow the best graph by two with the remaining time.
    left = end - time.monotonic()
    if left > 2.0 and best[0] < moore:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, left - 1.5, 1],
                             stdin_graph=best, timeout=left + 3)
            n2, e2 = lib.parse_graph_text(text)
            if n2 > best[0] and lib.is_valid(n2, e2, d, D):
                best = (n2, e2)
        except Exception:
            pass
    return best
