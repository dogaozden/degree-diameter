"""Abelian and metacyclic lift search with a fresh group family, plus a safe fallback.

Construction: a 2p-fibre bipartite lift over a group G of order N, with a d-regular base multigraph
on p + p vertices (p = 1 or 2). Each attempt draws G from one of two families: a direct product
Z_A x Z_B (abelian, one third of the draws) or a metacyclic Z_m x|_r Z_k (the rest). Voltages are
annealed against an exact orbit-reduced diameter count: BFS from the 2p fibre identities only, since
left multiplication is a regular automorphism on each fibre. Successes are validated with the full
bitset check.

Orders are chosen in two modes: near the record or goal (best + 2 once the record is matched), and
just above the current best, which climbs slowly from weak starts. The C engine never touches the
start graph unless it is valid and strictly larger.

Python builds the best algebraic start (PG(2,q), W(q), Araujo-Pardo-Lopez, or K_{d,d}), checks it
with lib.is_valid, and accepts the C output only if it is valid and strictly larger.
"""
import itertools
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

#define MAXN 12000
#define MAXD 32
#define MAXW ((MAXN + 63) / 64)
#define MAXP 2
#define MAXDART (MAXD * MAXP)
#define MAXG 3300

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct { int type, A, B, r; } GDesc;

static int d, D;
static long MOORE;
static long target_n = 0;
static double t_end;

static int GN;
static unsigned short GT[MAXG * MAXG];
static int RP[MAXG];

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

/* Group multiplication table. Type 0: Z_A x Z_B, element a*B+c.
 * Type 1: Z_A x|_r Z_B, element a*B+b, (a,b)(c,e) = (a + r^b c, b + e). Identity is index 0. */
static void build_table(const GDesc *G, int N) {
    GN = N;
    if (G->type == 0) {
        int A = G->A, B = G->B;
        for (int x = 0; x < N; x++) {
            int a = x / B, c = x % B;
            for (int y = 0; y < N; y++) {
                int b = y / B, e = y % B;
                GT[x * N + y] = (unsigned short)(((a + b) % A) * B + (c + e) % B);
            }
        }
    } else {
        int m = G->A, k = G->B, r = G->r;
        RP[0] = 1 % m;
        for (int b = 1; b < k; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
        for (int x = 0; x < N; x++) {
            int a = x / k, b = x % k;
            for (int y = 0; y < N; y++) {
                int c = y / k, e = y % k;
                long val = ((long)a + (long)RP[b] * c) % m;
                GT[x * N + y] = (unsigned short)(val * k + (b + e) % k);
            }
        }
    }
}

/* Abelian with probability 1/3 (uniform over divisors), else uniform metacyclic. */
static int pick_group(int N, GDesc *G) {
    if (rndint(3) == 0) {
        int c = 0;
        for (int a = 1; a <= N; a++) if (N % a == 0) c++;
        int t = rndint(c);
        int A = 1;
        for (int a = 1; a <= N; a++)
            if (N % a == 0) { if (t == 0) { A = a; break; } t--; }
        G->type = 0; G->A = A; G->B = N / A; G->r = 0;
        return 1;
    }
    long count = 0;
    int found = 0;
    for (int m = 2; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1) continue;
            count++;
            if (rndint((int)count) == 0) {
                G->type = 1; G->A = m; G->B = k; G->r = r;
                found = 1;
            }
        }
    }
    if (!found) {
        G->type = 0; G->A = 1; G->B = N; G->r = 0;
    }
    return 1;
}

static int di[MAXDART], dj[MAXDART], dg[MAXDART];

/* d random permutations of the p fibres: one dart per fibre per permutation. */
static void make_darts(int p) {
    int nd = 0;
    for (int s = 0; s < d; s++) {
        int perm[MAXP];
        for (int i = 0; i < p; i++) perm[i] = i;
        for (int i = p - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < p; i++) { di[nd] = i; dj[nd] = perm[i]; nd++; }
    }
}

static int clashes(int t, int g, int nd) {
    for (int s = 0; s < nd; s++)
        if (s != t && di[s] == di[t] && dj[s] == dj[t] && dg[s] == g) return 1;
    return 0;
}

/* A-fibre i element x -> i*N + x; B-fibre j element x -> (p+j)*N + x. */
static void build_lift(Graph *g, int p, int N, int nd) {
    int S = p * N;
    g->n = 2 * S;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= S; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, di[t] * N + x, S + dj[t] * N + GT[x * N + dg[t]]);
}

static int dist_buf[MAXN], queue_buf[MAXN];

/* Sum over the 2p fibre identities of unreached vertices within distance D. */
static long orbit_bad(const Graph *g, int p, int N) {
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

static long anneal(Graph *g, int p, int N, int nd, int maxit, double until) {
    build_lift(g, p, N, nd);
    long bad = orbit_bad(g, p, N);
    double T = 1.0;
    for (int it = 0; it < maxit && bad > 0; it++) {
        if ((it & 63) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = dg[t];
        int ng = rndint(N);
        if (ng == old || clashes(t, ng, nd)) continue;
        dg[t] = ng;
        build_lift(g, p, N, nd);
        long nb = orbit_bad(g, p, N);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
        else dg[t] = old;
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    build_lift(g, p, N, nd);
    return bad;
}

static int attempt(Graph *best, int p, int N, double until) {
    static Graph cand;
    GDesc G;
    int nd = p * d;
    while (now() < until) {
        pick_group(N, &G);
        build_table(&G, N);
        make_darts(p);
        for (int t = 0; t < nd; t++) dg[t] = -1;
        for (int t = 0; t < nd; t++) {
            int g;
            do { g = rndint(N); } while (clashes(t, g, nd));
            dg[t] = g;
        }
        long bad = anneal(&cand, p, N, nd, 8000, until);
        if (bad == 0 && cand.n > best->n && is_valid(&cand)) {
            copy_graph(best, &cand);
            return 1;
        }
    }
    return 0;
}

/* Goal mode: order near the record (or best + 2 once reached). Climb mode: just above best.
 * Both use p in {1, 2}; any infeasible draw falls back to p = 1 with a small order. */
static void search(Graph *best, double until) {
    while (now() < until) {
        if (best->n + 2 > MOORE) return;
        int p = rndint(2) ? 1 : 2;
        long goal = (target_n > best->n) ? target_n : best->n + 2;
        long N;
        if (rndint(2) == 0)
            N = (goal + 2L * p - 1) / (2L * p) + rndint(3);
        else
            N = best->n / (2L * p) + 1 + rndint(8);
        if (N < d) N = d;
        if (N > MAXG || 2L * p * N > MAXN || 2L * p * N > MOORE) {
            p = 1;
            N = best->n / 2 + 1 + rndint(8);
            if (N < d) N = d;
            if (N > MAXG || 2L * N > MAXN || 2L * N > MOORE) return;
        }
        double left = until - now();
        if (left < 0.05) break;
        double sl = left < 4.0 ? left : 4.0;
        attempt(best, p, (int)N, now() + sl);
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
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    MOORE = moore_bound();
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    if (D >= 2 && best.n < MOORE) search(&best, t_end);
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

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if budget <= 0.5:
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
