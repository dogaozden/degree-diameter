"""Bi-Cayley/voltage-lift search with symmetry-reduced annealing.

The search only builds lifts of a small base multigraph over a group G = Z_m x| Z_k.
Left multiplication by G is an automorphism of every such lift, so the diameter test
needs one BFS per base vertex (2p BFS in total) instead of one per vertex. Voltages
are then annealed directly against the number of unreached vertices, with an adaptive
target order. Python keeps a validated fallback, so every case returns a valid graph.
"""
import time

import lib

C_SOURCE = r'''
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 8192
#define MAXDEG 40
#define MAXP 4
#define MAXD 32
#define MAXGN 1100

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN * MAXDEG];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;
static Graph best, work;
static int mark[MAXN], lvl[MAXN], que[MAXN];
static int mstamp = 0;

/* ---------------------------------------------------------------- utilities */

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_i(int a, int b) {
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

/* ---------------------------------------------------------------- graph basics */

/* Number of vertices within distance D of s (BFS, stops at depth D). */
static int bfs_reach(const Graph *g, int s) {
    int head = 0, tail = 0;
    if (++mstamp == 0x7fffffff) {
        memset(mark, 0, sizeof mark);
        mstamp = 1;
    }
    mark[s] = mstamp;
    lvl[s] = 0;
    que[tail++] = s;
    while (head < tail) {
        int v = que[head++];
        if (lvl[v] >= D) continue;
        const int *a = g->adj + (size_t)v * MAXDEG;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = a[i];
            if (mark[u] != mstamp) {
                mark[u] = mstamp;
                lvl[u] = lvl[v] + 1;
                que[tail++] = u;
            }
        }
    }
    return tail;
}

/* Full check: simple, bipartite by side labels, degree <= d, diameter <= D. */
static int full_valid(const Graph *g) {
    int n = g->n;
    if (n <= 0 || n > MAXN) return 0;
    for (int v = 0; v < n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v * MAXDEG + i];
            if (u < 0 || u >= n || u == v || g->side[u] == g->side[v]) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v * MAXDEG + j] == u) return 0;
        }
    }
    if (n == 1) return 1;
    for (int v = 0; v < n; v++)
        if (bfs_reach(g, v) != n) return 0;
    return 1;
}

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj + (size_t)v * MAXDEG, src->adj + (size_t)v * MAXDEG,
               sizeof(int) * src->deg[v]);
    }
}

static void print_graph(const Graph *g) {
    long m = 0;
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u * MAXDEG + i]) m++;
    printf("%d %ld\n", g->n, m);
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++) {
            int v = g->adj[u * MAXDEG + i];
            if (u < v) printf("%d %d\n", u, v);
        }
}

/* K_{d,d}: valid for D >= 2. */
static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = v >= d;
    }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) {
            int x = a, y = d + b;
            g->adj[x * MAXDEG + g->deg[x]++] = y;
            g->adj[y * MAXDEG + g->deg[y]++] = x;
        }
}

/* Reads "n m" + edges; keeps the graph only if it is fully valid. */
static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
    for (int v = 0; v < n; v++) {
        g->deg[v] = 0;
        g->side[v] = 0;
    }
    g->n = n;
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n || u == v ||
            g->deg[u] >= MAXDEG || g->deg[v] >= MAXDEG) {
            g->n = 0;
            return;
        }
        g->adj[u * MAXDEG + g->deg[u]++] = v;
        g->adj[v * MAXDEG + g->deg[v]++] = u;
    }
    static int col[MAXN], qq[MAXN];
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        int head = 0, tail = 0;
        col[s] = 0;
        qq[tail++] = s;
        while (head < tail) {
            int v = qq[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v * MAXDEG + i];
                if (col[u] < 0) {
                    col[u] = 1 - col[v];
                    qq[tail++] = u;
                } else if (col[u] == col[v]) {
                    g->n = 0;
                    return;
                }
            }
        }
    }
    for (int v = 0; v < n; v++) g->side[v] = (unsigned char)col[v];
    if (!full_valid(g)) g->n = 0;
}

/* ---------------------------------------------------------------- groups */

/* Z_m x|_r Z_k, element (a,b) coded a*k+b, (a,b)(c,e) = (a + r^b c, b + e). Identity is 0. */
static int GN, GM, GK, GR;
static int *MUL = NULL;
static int rpw[MAXGN + 1];

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    return (int)(((long)a + (long)rpw[b] * c) % GM) * GK + (b + e) % GK;
}

static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GR = r;
    GN = m * k;
    rpw[0] = 1 % m;
    for (int b = 1; b < k; b++) rpw[b] = (int)((long)rpw[b - 1] * r % m);
    free(MUL);
    MUL = malloc(sizeof(int) * (size_t)GN * GN);
    for (int x = 0; x < GN; x++)
        for (int y = 0; y < GN; y++) MUL[x * GN + y] = gmul(x, y);
}

/* Uniformly random (m, k, r) with m*k = N, gcd(r, m) = 1, r^k = 1 mod m. */
static int pick_group(int N, int *pm, int *pk, int *pr) {
    long cnt = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd_i(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            cnt++;
            if (rndint((int)(cnt < 2000000000L ? cnt : 2000000000L)) == 0) {
                *pm = m;
                *pk = k;
                *pr = r;
            }
        }
    }
    return cnt > 0;
}

/* ---------------------------------------------------------------- voltage lifts */

static int P;                       /* base vertices per side */
static int nd;                      /* number of darts = P * d */
static int dI[MAXP * MAXD], dJ[MAXP * MAXD], dG[MAXP * MAXD];

/* True if some other dart between the same base pair already has voltage g. */
static int clash(int t, int g) {
    for (int s = 0; s < nd; s++)
        if (s != t && dI[s] == dI[t] && dJ[s] == dJ[t] && dG[s] == g) return 1;
    return 0;
}

/* Random d-regular bipartite base multigraph with p vertices per side, connected. */
static void make_base(int p) {
    int M[MAXP][MAXP];
    for (;;) {
        memset(M, 0, sizeof M);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i];
                perm[i] = perm[j];
                perm[j] = s;
            }
            for (int i = 0; i < p; i++) M[i][perm[i]]++;
        }
        int seen[2 * MAXP], stack[2 * MAXP], top = 0, cnt = 1;
        memset(seen, 0, sizeof seen);
        seen[0] = 1;
        stack[top++] = 0;
        while (top) {
            int v = stack[--top];
            for (int u = 0; u < 2 * p; u++) {
                if (seen[u]) continue;
                int linked = v < p ? (u >= p && M[v][u - p] > 0) : (u < p && M[u][v - p] > 0);
                if (linked) {
                    seen[u] = 1;
                    cnt++;
                    stack[top++] = u;
                }
            }
        }
        if (cnt == 2 * p) break;
    }
    P = p;
    nd = 0;
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dI[nd] = i;
                dJ[nd] = j;
                dG[nd] = -1;
                nd++;
            }
    for (int t = 0; t < nd; t++) {
        do {
            dG[t] = rndint(GN);
        } while (clash(t, dG[t]));
    }
}

/* Lift: A-vertex (i,x) = i*GN+x, B-vertex (j,y) = P*GN + j*GN + y.
 * Dart (i,j,g) joins (i,x) to (j, x*g) for all x. */
static void build_graph(Graph *g) {
    int p = P, N = GN;
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = v >= p * N;
    }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++) {
            int a = dI[t] * N + x;
            int b = p * N + dJ[t] * N + MUL[x * N + dG[t]];
            g->adj[a * MAXDEG + g->deg[a]++] = b;
            g->adj[b * MAXDEG + g->deg[b]++] = a;
        }
}

/* Left multiplication is an automorphism, so orbit representatives suffice:
 * the cost is the total number of vertices not reached within D from the 2P representatives. */
static long lift_cost(void) {
    build_graph(&work);
    long c = 0;
    for (int i = 0; i < P; i++) {
        c += work.n - bfs_reach(&work, i * GN);
        c += work.n - bfs_reach(&work, P * GN + i * GN);
    }
    return c;
}

/* Simulated annealing over the voltages of the current base. On success work holds the lift. */
static int anneal(long steps, double until) {
    long cur = lift_cost();
    const double T0 = 2.0, T1 = 0.05;
    for (long s = 0; s < steps && cur > 0; s++) {
        if ((s & 127) == 0 && now() > until) return 0;
        double T = T0 * pow(T1 / T0, (double)s / (double)steps);
        int t = rndint(nd);
        int old = dG[t];
        int g = rndint(GN);
        if (g == old || clash(t, g)) continue;
        dG[t] = g;
        long nc = lift_cost();
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
        } else {
            dG[t] = old;
        }
    }
    if (cur != 0) return 0;
    build_graph(&work);
    return 1;
}

static int attempt(int p, long N, long steps, double until) {
    int m, k, r;
    if (!pick_group((int)N, &m, &k, &r)) return 0;
    set_group(m, k, r);
    make_base(p);
    return anneal(steps, until);
}

/* ---------------------------------------------------------------- main */

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
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1) {
        printf("1 0\n");
        return 0;
    }
    if (D < 2 || d == 1 || d > MAXD) {
        printf("2 1\n0 1\n");
        return 0;
    }

    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!full_valid(&best)) complete_bipartite(&best);

    long moore = moore_bound();
    double step = 32.0;
    int skips = 0;
    while (now() < t_end && best.n + 2 <= moore) {
        long target = best.n + (long)step;
        if (target > moore) target = moore;
        int p = 1 + rndint(MAXP);
        long N = (target + 2 * p - 1) / (2 * p) + rndint(2);
        long minN = best.n / (2 * p) + 1;
        if (N < minN) N = minN;
        if (N < d + 1) N = d + 1;
        if (N > MAXGN || 2L * p * N > MAXN || 2L * p * N > moore) {
            if (++skips > 1000) break;
            continue;
        }
        skips = 0;
        double left = t_end - now();
        double slice = left < 4.0 ? left : 4.0;
        if (slice <= 0) break;
        double until = now() + slice;
        if (attempt(p, N, 60000, until) && work.n > best.n && full_valid(&work)) {
            copy_graph(&best, &work);
            step *= 2;
            if (step > 4096) step = 4096;
        } else {
            step /= 2;
            if (step < 2) step = 2;
        }
    }

    if (!full_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def fallback(d, D):
    """A small graph that is valid for (d, D)."""
    candidates = []
    if d >= 1:
        candidates.append(lib.haar_graph(d, range(d)))  # K_{d,d}
    candidates.append((2, [(0, 1)]))
    candidates.append((1, []))
    for cand in candidates:
        if lib.is_valid(*cand, d, D):
            return cand
    return (1, [])


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    best = fallback(d, D)
    start = known_start(d, D)
    if start is not None and start[0] > best[0] and lib.is_valid(*start, d, D):
        best = start
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph
    if budget > 0.5:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=start, timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(*out, d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
