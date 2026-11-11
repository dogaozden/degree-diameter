"""Bi-Cayley search over non-metacyclic groups (Heisenberg(p) x Z_k) plus metacyclic groups.

Different construction from the parent: instead of sampling only metacyclic groups, each attempt
picks either a metacyclic group Z_m x|_r Z_k or a Heisenberg-type group Heis(p) x Z_k (p in
{2,3,5,7}, order p^3 k). The graph is a lift with P fibres per side (P = 1 or 2) and d darts per
fibre, voltages in the group. Left multiplication is a regular automorphism on every fibre, so
diameter is checked by BFS from one identity per fibre (2P sources), with simulated annealing on
the unreached-pair count. The search climbs from the current best order upward.

Risk: the search space differs from the parent's, so it may underperform the 2184 record in 60 s.
Safety: C errors and timeouts are caught, and every returned graph passes lib.is_valid. The
fallback is the best algebraic start (K_{d,d}, PG(2,d-1), or W(q)).
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
    int type;      /* 0: metacyclic Z_m x| Z_k, 1: Heisenberg(p) x Z_k */
    int N, m, k, r, p;
    int rp[MAXN];
} Grp;

static int d, D;
static long MOORE;
static double t_end;
static uint64_t rng_state = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

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

static int has_edge(const Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) return 1;
    return 0;
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

/* ---------- groups ---------- */

static void set_meta(Grp *G, int m, int k, int r) {
    G->type = 0; G->m = m; G->k = k; G->r = r; G->N = m * k; G->p = 1;
    G->rp[0] = 1 % m;
    for (int b = 1; b < k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * r % m);
}

static void set_heis(Grp *G, int p, int k) {
    G->type = 1; G->p = p; G->k = k; G->m = 1; G->r = 0; G->N = p * p * p * k;
}

static int gmul(const Grp *G, int x, int y) {
    if (G->type == 0) {
        int k = G->k;
        int a = x / k, b = x % k, c = y / k, e = y % k;
        return (int)(((long)a + (long)G->rp[b] * c) % G->m) * k + (b + e) % k;
    }
    int p = G->p, k = G->k;
    int z1 = x % k, t1 = x / k, c1 = t1 % p, b1 = (t1 / p) % p, a1 = t1 / (p * p);
    int z2 = y % k, t2 = y / k, c2 = t2 % p, b2 = (t2 / p) % p, a2 = t2 / (p * p);
    int A = (a1 + a2) % p;
    int B = (b1 + b2) % p;
    int C = (c1 + c2 + a1 * b2) % p;
    int Z = (z1 + z2) % k;
    return ((A * p + B) * p + C) * k + Z;
}

static void pick_meta(int N, Grp *G) {
    for (int tries = 0; tries < 30; tries++) {
        int divs[64], nd = 0;
        for (int m = 1; m <= N && nd < 64; m++)
            if (N % m == 0) divs[nd++] = m;
        int m = divs[rndint(nd)];
        int k = N / m;
        if (m == 1) { set_meta(G, 1, N, 1); return; }
        int cnt = 0, pick = -1;
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1) continue;
            cnt++;
            if (rndint(cnt) == 0) pick = r;
        }
        if (pick > 0) { set_meta(G, m, k, pick); return; }
    }
    set_meta(G, 1, N, 1);
}

static void pick_group(int N, Grp *G) {
    static const int pr[4] = {2, 3, 5, 7};
    int ps[4], np = 0;
    for (int i = 0; i < 4; i++) {
        long c = (long)pr[i] * pr[i] * pr[i];
        if (N % c == 0) ps[np++] = pr[i];
    }
    if (np > 0 && rndint(2) == 0) {
        int p = ps[rndint(np)];
        set_heis(G, p, N / (p * p * p));
    } else {
        pick_meta(N, G);
    }
}

/* ---------- voltage lifts ---------- */

static int di[MAXDART], dj[MAXDART], dg[MAXDART];

static void make_darts(int P) {
    int nd = 0;
    for (int s = 0; s < d; s++) {
        int perm[MAXP];
        for (int i = 0; i < P; i++) perm[i] = i;
        for (int i = P - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < P; i++) { di[nd] = i; dj[nd] = perm[i]; nd++; }
    }
}

static int clashes(int t, int g, int nd) {
    for (int s = 0; s < nd; s++)
        if (s != t && di[s] == di[t] && dj[s] == dj[t] && dg[s] == g) return 1;
    return 0;
}

static int dup_before(int t, int g) {
    for (int s = 0; s < t; s++)
        if (di[s] == di[t] && dj[s] == dj[t] && dg[s] == g) return 1;
    return 0;
}

/* A-fibre i element x -> i*N + x; B-fibre j element x -> (P+j)*N + x. */
static void build_lift(Graph *g, int P, int N, const Grp *G, int nd) {
    int S = P * N;
    g->n = 2 * S;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= S; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, di[t] * N + x, S + dj[t] * N + gmul(G, x, dg[t]));
}

static int dist_buf[MAXN], queue_buf[MAXN];

/* Left multiplication is a regular automorphism on each fibre, so BFS from one identity per
 * fibre (2P sources) decides the diameter. Returns the total number of unreached pairs. */
static long orbit_bad(const Graph *g, int P, int N) {
    int nv = g->n;
    long total = 0;
    for (int b = 0; b < 2 * P; b++) {
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

static long anneal(Graph *g, int P, int N, const Grp *G, int nd, long maxit, double until) {
    static int bestdg[MAXDART];
    build_lift(g, P, N, G, nd);
    long bad = orbit_bad(g, P, N);
    long bestbad = bad;
    memcpy(bestdg, dg, sizeof(int) * nd);
    double T = 2.0;
    for (long it = 0; it < maxit && bestbad > 0; it++) {
        if ((it & 31) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = dg[t];
        int ng = rndint(N);
        if (ng == old || clashes(t, ng, nd)) continue;
        dg[t] = ng;
        int t2 = -1, old2 = 0;
        if (rndint(4) == 0) {
            t2 = rndint(nd);
            if (t2 == t) t2 = -1;
        }
        if (t2 >= 0) {
            old2 = dg[t2];
            int ng2 = rndint(N);
            if (ng2 == old2 || clashes(t2, ng2, nd)) { dg[t] = old; continue; }
            dg[t2] = ng2;
        }
        build_lift(g, P, N, G, nd);
        long nb = orbit_bad(g, P, N);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
            if (bad < bestbad) {
                bestbad = bad;
                memcpy(bestdg, dg, sizeof(int) * nd);
            }
        } else {
            dg[t] = old;
            if (t2 >= 0) dg[t2] = old2;
        }
        T *= 0.9995;
        if (T < 0.05) T = 2.0;
    }
    memcpy(dg, bestdg, sizeof(int) * nd);
    build_lift(g, P, N, G, nd);
    return bestbad;
}

/* Random restarts (new group, new darts, new voltages) at fibre size N until the slice ends. */
static int attempt(Graph *best, int P, int N, double until) {
    static Graph cand;
    static Grp G;
    int nd = P * d;
    if (N < 2 * d + 2) return 0;
    while (now() < until) {
        pick_group(N, &G);
        make_darts(P);
        for (int t = 0; t < nd; t++) {
            int g;
            do { g = rndint(N); } while (dup_before(t, g));
            dg[t] = g;
        }
        long bad = anneal(&cand, P, N, &G, nd, 400000, until);
        if (bad == 0 && cand.n > best->n && is_valid(&cand)) {
            copy_graph(best, &cand);
            return 1;
        }
    }
    return 0;
}

static void search(Graph *best, double until) {
    while (now() < until) {
        int P = (rndint(10) < 6) ? 1 : 2;
        long N = best->n / (2L * P) + 1 + rndint(3);
        if (2L * P * N > MOORE || 2L * P * N > MAXN) {
            P = 1;
            N = best->n / 2 + 1 + rndint(3);
        }
        if (2L * P * N > MOORE || 2L * P * N > MAXN) return;
        double left = until - now();
        double sl = left < 3.0 ? left : 3.0;
        if (sl < 0.1) return;
        attempt(best, P, (int)N, now() + sl);
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
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }
    MOORE = moore_bound();
    read_start(&best);
    if (best.n == 0 || !is_valid(&best)) complete_bipartite(&best);
    if (D >= 2 && best.n < MOORE) search(&best, t_end);
    if (!is_valid(&best)) complete_bipartite(&best);
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
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 0.2:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
