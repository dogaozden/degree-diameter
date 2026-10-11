"""Bi-Cayley search over small groups: a different construction from the lift search.

Sides are A_g and B_g for g in a group G, with A_g ~ B_{g s} for s in a d-element set S.
Left multiplication is an automorphism, so diameter <= D only needs BFS from A_1 and B_1.
Groups are cyclic, dihedral, or PSL/PGL(2, p) for small primes p, built in C.
Phase 1 (group search) runs simulated annealing over S for each candidate group.
Phase 2 (grow by two) anneals from the best graph with the remaining time.
Fallbacks: known constructions, then K_{d,d}. Every returned graph is checked with lib.is_valid.
"""
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley group search core.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Phase 1: for a group G of order N (cyclic, dihedral, PSL(2,p), PGL(2,p)), choose a
 *   d-element set S in G and form the graph on A_g, B_g (g in G) with A_g ~ B_{g s}.
 *   Cost = unreached pairs from A_1 and B_1 within distance D. Annealed by swaps in S.
 * Phase 2: grow by two from the best graph, then anneal degree-preserving swaps.
 */
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
#define MAXG 1024
#define MAXC 4096

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;
static long moore;
static Graph best;

/* ------------------------------------------------------------------ utilities */

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

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    if (b < 0) b += m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static long compute_moore(void) {
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

/* ------------------------------------------------------------------ graph basics */

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

/* ------------------------------------------------------------------ distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Number of unordered pairs at distance > D. Bitset reachability, D rounds. */
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

/* Full validity: simple, bipartite by side labels, degree <= d, diameter <= D. */
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

/* ------------------------------------------------------------------ input / output */

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
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

/* K_{d,d}: valid for D >= 2. */
static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------------ groups */

static int GN, GID;
static int MT[MAXG * MAXG];   /* MT[x*N+y] = x*y */
static int INVG[MAXG];

static void finish_group(int N, int id) {
    GN = N;
    GID = id;
    for (int x = 0; x < N; x++) INVG[x] = -1;
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MT[x * N + y] == id) INVG[x] = y;
}

static void setup_cyclic(int N) {
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            MT[x * N + y] = (x + y) % N;
    finish_group(N, 0);
}

/* Dihedral of order 2m: element 2r+f stands for r^a s^f. */
static void setup_dihedral(int m) {
    int N = 2 * m;
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++) {
            int r1 = x / 2, f1 = x & 1, r2 = y / 2, f2 = y & 1;
            int r = f1 ? ((r1 - r2) % m + m) % m : (r1 + r2) % m;
            MT[x * N + y] = 2 * r + (f1 ^ f2);
        }
    finish_group(N, 0);
}

static int imod(long x, int p) {
    x %= p;
    if (x < 0) x += p;
    return (int)x;
}

static int MIDX[14641];       /* p^4 for p <= 11 */
static int MEL[MAXG][4];

/* PGL(2,p) (psl = 0) or PSL(2,p) (psl = 1) as normalized matrices. Returns order or 0. */
static int setup_matrix(int p, int psl) {
    int P4 = p * p * p * p;
    int sq[16];
    memset(sq, 0, sizeof sq);
    for (int k = 1; k < p; k++) sq[(k * k) % p] = 1;
    for (int i = 0; i < P4; i++) MIDX[i] = -1;
    int N = 0;
    for (int a = 0; a < p; a++)
        for (int b = 0; b < p; b++)
            for (int c = 0; c < p; c++)
                for (int e = 0; e < p; e++) {
                    int det = imod((long)a * e - (long)b * c, p);
                    if (det == 0) continue;
                    if (psl && !sq[det]) continue;
                    int v[4] = {a, b, c, e};
                    int f = 0;
                    for (int i = 0; i < 4; i++)
                        if (v[i]) { f = v[i]; break; }
                    if (f != 1) continue;
                    if (N >= MAXG) return 0;
                    MIDX[((a * p + b) * p + c) * p + e] = N;
                    for (int i = 0; i < 4; i++) MEL[N][i] = v[i];
                    N++;
                }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++) {
            const int *A = MEL[x], *B = MEL[y];
            int m[4];
            m[0] = imod((long)A[0] * B[0] + (long)A[1] * B[2], p);
            m[1] = imod((long)A[0] * B[1] + (long)A[1] * B[3], p);
            m[2] = imod((long)A[2] * B[0] + (long)A[3] * B[2], p);
            m[3] = imod((long)A[2] * B[1] + (long)A[3] * B[3], p);
            int f = 0;
            for (int i = 0; i < 4; i++)
                if (m[i]) { f = m[i]; break; }
            if (f == 0) return 0;
            long iv = powmod(f, p - 2, p);
            for (int i = 0; i < 4; i++) m[i] = imod((long)m[i] * iv, p);
            int key = ((m[0] * p + m[1]) * p + m[2]) * p + m[3];
            if (MIDX[key] < 0) return 0;
            MT[x * N + y] = MIDX[key];
        }
    int id = MIDX[((1 * p + 0) * p + 0) * p + 1];
    if (id < 0) return 0;
    finish_group(N, id);
    return N;
}

typedef struct {
    int type;   /* 0 cyclic (a = N), 1 dihedral (a = m), 2 matrix (a = p, psl) */
    int N, a, psl;
} Cand;

static Cand cand[MAXC];
static int ncand;

static void build_candidates(int hi) {
    ncand = 0;
    static const int primes[4] = {11, 7, 5, 3};   /* descending, so orders descend */
    for (int pi = 0; pi < 4; pi++) {
        int p = primes[pi];
        for (int psl = 0; psl < 2; psl++) {
            int N = p * (p * p - 1) / (psl ? 2 : 1);
            if (N >= d && N <= hi && ncand < MAXC) {
                cand[ncand].type = 2;
                cand[ncand].N = N;
                cand[ncand].a = p;
                cand[ncand].psl = psl;
                ncand++;
            }
        }
    }
    for (int m = hi / 2; m >= 3; m--) {
        int N = 2 * m;
        if (N >= d && N <= hi && ncand < MAXC) {
            cand[ncand].type = 1;
            cand[ncand].N = N;
            cand[ncand].a = m;
            cand[ncand].psl = 0;
            ncand++;
        }
    }
    for (int N = hi; N >= d; N--)
        if (ncand < MAXC) {
            cand[ncand].type = 0;
            cand[ncand].N = N;
            cand[ncand].a = N;
            cand[ncand].psl = 0;
            ncand++;
        }
}

static int setup_candidate(const Cand *c) {
    if (c->type == 0) { setup_cyclic(c->N); return c->N; }
    if (c->type == 1) { setup_dihedral(c->a); return 2 * c->a; }
    return setup_matrix(c->a, c->psl);
}

/* ------------------------------------------------------------------ bi-Cayley search */

static int Sel[MAXD];
static int qbuf[2 * MAXG];
static int visst[2 * MAXG];
static int vstamp = 0;

/* Vertices reached within D steps from A_idx (side 0) or B_idx (side 1); returns unreached count. */
static int unreached_from(int side, int idx) {
    int N = GN, n = 2 * N;
    if (++vstamp == 0x7fffffff) {
        memset(visst, 0, sizeof visst);
        vstamp = 1;
    }
    int src = side ? N + idx : idx;
    int head = 0, tail = 0;
    visst[src] = vstamp;
    qbuf[tail++] = src;
    for (int lev = 0; lev < D && head < tail; lev++) {
        int end = tail;
        while (head < end) {
            int u = qbuf[head++];
            if (u < N) {
                for (int k = 0; k < d; k++) {
                    int v = N + MT[u * N + Sel[k]];
                    if (visst[v] != vstamp) { visst[v] = vstamp; qbuf[tail++] = v; }
                }
            } else {
                int y = u - N;
                for (int k = 0; k < d; k++) {
                    int v = MT[y * N + INVG[Sel[k]]];
                    if (visst[v] != vstamp) { visst[v] = vstamp; qbuf[tail++] = v; }
                }
            }
        }
    }
    return n - tail;
}

static long group_cost(void) {
    return (long)unreached_from(0, GID) + (long)unreached_from(1, GID);
}

static void random_S(void) {
    int N = GN;
    for (int k = 0; k < d; k++) {
        int r, ok;
        do {
            r = rndint(N);
            ok = 1;
            for (int j = 0; j < k; j++)
                if (Sel[j] == r) { ok = 0; break; }
        } while (!ok);
        Sel[k] = r;
    }
}

static int build_group_graph(Graph *g) {
    int N = GN;
    g->n = 2 * N;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = v >= N;
    }
    for (int x = 0; x < N; x++)
        for (int k = 0; k < d; k++)
            add_edge(g, x, N + MT[x * N + Sel[k]]);
    return is_valid(g);
}

/* Anneal the set S in the current group until cost 0 or `until`. */
static void try_group(double until) {
    static Graph cg;
    int N = GN;
    random_S();
    long c = group_cost();
    double T = 2.0;
    long steps = 0, last = 0, bestc = c;
    while (c > 0) {
        if ((steps & 255) == 0 && now() > until) break;
        steps++;
        int k = rndint(d), g = rndint(N);
        int dup = 0;
        for (int j = 0; j < d; j++)
            if (Sel[j] == g) { dup = 1; break; }
        if (dup) continue;
        int old = Sel[k];
        Sel[k] = g;
        long c2 = group_cost();
        if (c2 <= c || rnd01() < exp((double)(c - c2) / T)) {
            c = c2;
            if (c < bestc) { bestc = c; last = steps; }
        } else {
            Sel[k] = old;
        }
        T *= 0.9995;
        if (T < 0.05) T = 2.0;
        if (steps - last > 20000) {
            random_S();
            c = group_cost();
            bestc = c;
            last = steps;
            T = 2.0;
        }
    }
    if (c == 0 && build_group_graph(&cg) && cg.n > best.n) copy_graph(&best, &cg);
}

static void group_phase(double until) {
    int hi = (int)(moore / 2);
    if (hi > MAXG) hi = MAXG;
    if (hi < d) return;
    build_candidates(hi);
    for (;;) {
        int any = 0;
        for (int ci = 0; ci < ncand && now() < until; ci++) {
            const Cand *c = &cand[ci];
            if (2 * c->N <= best.n) continue;
            if (2L * c->N > moore) continue;
            int N = setup_candidate(c);
            if (N != c->N) continue;
            any = 1;
            double slice = c->type == 2 ? 4.0 : (c->type == 1 ? 0.15 : 0.1);
            double e = now() + slice;
            if (e > until) e = until;
            try_group(e);
        }
        if (!any || now() >= until) break;
    }
}

/* ------------------------------------------------------------------ grow by two */

static int grow_once(const Graph *base, Graph *work, double until) {
    int n = base->n;
    if (n + 2 > moore || n + 2 > MAXN) return 0;
    copy_graph(work, base);
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
    int k = 0;
    for (int tries = 0; k < d - 1 && tries < 100000; tries++) {
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

static void grow_search(double until) {
    static Graph work;
    while (now() < until && best.n + 2 <= moore) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(&best, &work, now() + slice)) copy_graph(&best, &work);
    }
}

/* ------------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    if (d < 1 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();
    moore = compute_moore();

    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (best.n < moore) {
        group_phase(t0 + (t_end - t0) * 0.8);
        grow_search(t_end);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _known_start(d, D):
    """Best directly constructible graph for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record family 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return (1, [])
    if D == 1:
        return (2, [(0, 1)])

    best = lib.haar_graph(d, range(d))   # K_{d,d}: valid for D >= 2

    def consider(cand):
        nonlocal best
        if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand

    start = _known_start(d, D)
    if start is not None:
        consider(start)

    if best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 1.0:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 5)
        consider(lib.parse_graph_text(text))
    except (RuntimeError, ValueError):
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
