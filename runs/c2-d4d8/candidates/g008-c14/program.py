"""Base-graph rewiring plus voltage annealing over metacyclic groups.

Different from the parent's one-shot anneal: each attempt starts from a random d-regular bipartite base
multigraph on p + p fibres (p = 1 or 2). Annealing moves are of two kinds: change one dart's voltage, or
swap the B-endpoints of two darts (which keeps every fibre degree at d). Both keep darts pairwise distinct,
so the lift is simple. The cost is the number of pairs left beyond distance D, computed by BFS from the
fibre identities only (left-regular action). Successes are re-checked with the full bitset test.

Orders are chosen in two modes: a target band just above the record (record + 2 divided over the fibres),
and adaptive climbing from the current best. The Python side starts from the best algebraic graph,
checks it with lib.is_valid, and only accepts C output that is valid and strictly larger.
"""
import time
import itertools

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 8192
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXP 2
#define MAXDART (MAXD * MAXP)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct {
    int m, k, r;
    int rp[MAXN];
} Grp;

static int d, D;
static long MOORE;
static long target_n = 0;
static double t_end;
static Grp G;

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static int gcd(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

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

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
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

/* Number of unordered pairs at distance > D. */
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

/* Group element a*k+b, (a,b)(c,e) = (a + r^b c, b + e), with r^k = 1 mod m. */
static int gmul(int x, int y) {
    int a = x / G.k, b = x % G.k, c = y / G.k, e = y % G.k;
    return (int)(((long)a + (long)G.rp[b] * c) % G.m) * G.k + (b + e) % G.k;
}

/* Uniformly random metacyclic group of order N (reservoir sampling). */
static int pick_group(int N) {
    long count = 0;
    int bm = 0, bk = 0, br = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            count++;
            if (rndint((int)count) == 0) { bm = 1; bk = k; br = 1; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1) continue;
            count++;
            if (rndint((int)count) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (count == 0) return 0;
    G.m = bm; G.k = bk; G.r = br;
    G.rp[0] = 1 % bm;
    for (int b = 1; b < bk; b++) G.rp[b] = (int)((long)G.rp[b - 1] * br % bm);
    return 1;
}

/* Base multigraph: dart t joins A-fibre di[t] to B-fibre dj[t] with voltage dg[t].
 * Every fibre carries exactly d darts, so the lift is d-regular. */
static int di[MAXDART], dj[MAXDART], dg[MAXDART];

static int clash_prev(int t) {
    for (int s = 0; s < t; s++)
        if (di[s] == di[t] && dj[s] == dj[t] && dg[s] == dg[t]) return 1;
    return 0;
}

static int dup_free(int t, int nd) {
    for (int s = 0; s < nd; s++)
        if (s != t && di[s] == di[t] && dj[s] == dj[t] && dg[s] == dg[t]) return 0;
    return 1;
}

static void init_darts(int p, int N, int nd) {
    int t = 0;
    for (int s = 0; s < d; s++) {
        int perm[MAXP];
        for (int i = 0; i < p; i++) perm[i] = i;
        for (int i = p - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = perm[i]; perm[i] = perm[j]; perm[j] = tmp;
        }
        for (int i = 0; i < p; i++) { di[t] = i; dj[t] = perm[i]; t++; }
    }
    for (t = 0; t < nd; t++) {
        do { dg[t] = rndint(N); } while (clash_prev(t));
    }
}

/* Vertices: A-fibre i element x -> i*N + x; B-fibre j element x -> (p+j)*N + x. */
static void build_lift(Graph *g, int p, int N, int nd) {
    int S = p * N;
    g->n = 2 * S;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= S; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, di[t] * N + x, S + dj[t] * N + gmul(x, dg[t]));
}

static int dist_buf[MAXN], queue_buf[MAXN];

/* Left multiplication acts regularly on each fibre, so BFS from the 2p fibre identities suffices. */
static long orbit_bad(const Graph *g, int p, int N) {
    (void)N;
    int nv = g->n;
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

/* Annealing over voltage changes and B-endpoint swaps. Leaves the darts in the final state;
 * the caller must rebuild the lift from them. */
static long anneal(Graph *g, int p, int N, int nd, long maxit, double until) {
    build_lift(g, p, N, nd);
    long bad = orbit_bad(g, p, N);
    for (long it = 0; it < maxit && bad > 0; it++) {
        if ((it & 255) == 0 && now() > until) break;
        double T = 3.0 * (1.0 - (double)it / (double)maxit) + 0.05;
        int t = rndint(nd), s = rndint(nd);
        int sv_gt = dg[t], sv_gs = dg[s], sv_jt = dj[t], sv_js = dj[s];
        int mv = rndint(2);
        int ok;
        if (mv == 0) {
            int ng = rndint(N);
            if (ng == dg[t]) continue;
            dg[t] = ng;
            ok = dup_free(t, nd);
        } else {
            if (t == s || dj[t] == dj[s]) continue;
            int tmp = dj[t]; dj[t] = dj[s]; dj[s] = tmp;
            ok = dup_free(t, nd) && dup_free(s, nd);
        }
        if (!ok) {
            dg[t] = sv_gt; dg[s] = sv_gs; dj[t] = sv_jt; dj[s] = sv_js;
            continue;
        }
        build_lift(g, p, N, nd);
        long nb = orbit_bad(g, p, N);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            dg[t] = sv_gt; dg[s] = sv_gs; dj[t] = sv_jt; dj[s] = sv_js;
        }
    }
    return bad;
}

static int attempt(Graph *best, int p, int N, double until) {
    static Graph g;
    int nd = p * d;
    if (N < d) return 0;
    while (now() < until) {
        if (!pick_group(N)) return 0;
        init_darts(p, N, nd);
        long bad = anneal(&g, p, N, nd, 40000, until);
        build_lift(&g, p, N, nd);
        if (bad == 0 && g.n > best->n && is_valid(&g)) {
            copy_graph(best, &g);
            return 1;
        }
    }
    return 0;
}

static void search(Graph *best, double until) {
    long step = 1;
    while (now() < until) {
        if (best->n + 2 > MOORE) return;
        int p = (rndint(3) == 0) ? 2 : 1;
        int use_target = (target_n > 0 && best->n < target_n + 2 && rndint(2) == 0);
        long N;
        if (use_target) {
            long goal = target_n + 2;
            N = (goal + 2L * p - 1) / (2L * p) + rndint(3);
        } else {
            N = best->n / (2L * p) + step;
        }
        if (N < d) N = d;
        if (2L * p * N > MOORE || 2L * p * N > MAXN) {
            if (p == 2) continue;      /* retry, p = 1 is likelier */
            step = 1;                  /* climbing step too large: shrink it */
            continue;
        }
        double left = until - now();
        double sl = left / 6;
        if (sl < 0.5) sl = 0.5;
        if (sl > 4.0) sl = 4.0;
        if (sl > left) sl = left;
        int ok = attempt(best, p, (int)N, now() + sl);
        if (!use_target) {
            if (ok) { if (step < 64) step *= 2; }
            else if (step > 1) step /= 2;
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [target_n] < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    target_n = (argc >= 6) ? atol(argv[5]) : 0;
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) {
        printf("1 0\n");
        return 0;
    }
    static Graph best;
    MOORE = moore_bound();
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    if (D >= 2 && best.n < MOORE) {
        search(&best, t0 + (t_end - t0) * 0.97);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''

# Best known orders (targets for the record-jump phase in C).
RECORDS = {(3, 3): 14, (4, 8): 2184}


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


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])
    for cand in known_starts_safe(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 0.2:
        return best
    target = RECORDS.get((d, D), 0)
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget, target],
                         stdin_graph=best, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best


def known_starts_safe(d, D):
    try:
        return known_starts(d, D)
    except Exception:
        return []
