"""Degree-diameter search: exact constructions, then a C engine that anneals voltage lifts over
metacyclic groups Z_m x| Z_k of growing order. Block-transitive BFS gives an exact cost in O(blocks * V * d)."""
import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact constructions (calibration cases return immediately).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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
# C engine: anneal voltage lifts of d-regular bipartite base multigraphs
# (P blocks per side, d darts per source block) over Z_m x| Z_k.
# Moves: change a voltage, or swap the targets of two darts (keeps all degrees).
# Left multiplication is an automorphism, so the cost only needs BFS from the
# identity of each block: zero cost <=> diameter <= D.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
/* Degree-diameter search core.
 * Usage:  prog d D seed time_limit < start_graph
 * stdin:  "n m" + m edge lines (valid start), or "0 0".
 * stdout: "n m" + edge lines, the largest valid graph found.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXV 4096
#define MAXD 32
#define MAXW (MAXV / 64)
#define MAXP 6
#define MAXDART (MAXP * MAXD)
#define MAXG 2048

typedef struct {
    int n;
    int deg[MAXV];
    int adj[MAXV][MAXD];
    unsigned char side[MAXV];
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

static uint64_t RA[MAXV * MAXW], RB[MAXV * MAXW];
static int badv[MAXV];

/* Number of unordered pairs at distance > D (exact, full graph). */
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
    if (g->n <= 0 || g->n > MAXV) return 0;
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
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXV) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            g->deg[u] >= MAXD || g->deg[v] >= MAXD) { g->n = 0; return; }
        add_edge(g, u, v);
    }
    static int queue[MAXV];
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

/* ---------------- group Z_m x|_r Z_k, element (a,b) = a*k+b ---------------- */

#define GROUPMAX MAXG
static int GN;
static uint16_t MT[GROUPMAX * GROUPMAX];

static int build_group(int N) {
    int cnt = 0, bm = 1, bk = N, br = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            cnt++;
            if (rndint(cnt) == 0) { bm = 1; bk = k; br = 0; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            cnt++;
            if (rndint(cnt) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (!cnt) return 0;
    static int rp[GROUPMAX];
    rp[0] = 1 % bm;
    for (int b = 1; b < bk; b++) rp[b] = (int)((long)rp[b - 1] * br % bm);
    GN = N;
    for (int x = 0; x < N; x++) {
        int a = x / bk, b = x % bk;
        for (int y = 0; y < N; y++) {
            int c = y / bk, e = y % bk;
            int z = (int)((a + (long)rp[b] * c) % bm) * bk + (b + e) % bk;
            MT[x * N + y] = (uint16_t)z;
        }
    }
    return 1;
}

/* ---------------- lift state ---------------- */

static int P_, N_, V_, nd;
static int dI[MAXDART], dJ[MAXDART], dG[MAXDART];
static int nbr[MAXV][MAXD];
static int cntv[MAXV];

/* Dart t = i*d + l joins A_{i,x} to B_{j, x*g}. Each vertex gets exactly d neighbours. */
static void build_nbr(void) {
    for (int v = 0; v < V_; v++) cntv[v] = 0;
    for (int t = 0; t < nd; t++) {
        int ib = dI[t] * N_, jb = (P_ + dJ[t]) * N_, g = dG[t];
        for (int x = 0; x < N_; x++) {
            int a = ib + x, b = jb + MT[x * N_ + g];
            if (cntv[a] < d) nbr[a][cntv[a]++] = b;
            if (cntv[b] < d) nbr[b][cntv[b]++] = a;
        }
    }
}

static int vis[MAXV], vstamp = 0;
static int qb[MAXV];

/* Number of vertices within distance D of src. */
static int ballcount(int src) {
    int head = 0, tail = 0;
    vstamp++;
    qb[tail++] = src;
    vis[src] = vstamp;
    for (int depth = 0; depth < D && head < tail; depth++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qb[head];
            for (int k = 0; k < d; k++) {
                int u = nbr[v][k];
                if (vis[u] != vstamp) { vis[u] = vstamp; qb[tail++] = u; }
            }
        }
    }
    return tail;
}

/* Sum over block representatives of unreached vertices (zero iff diameter <= D). */
static long lift_cost(void) {
    build_nbr();
    long c = 0;
    for (int b = 0; b < 2 * P_; b++) c += V_ - ballcount(b * N_);
    return c;
}

/* True if some dart other than ex1, ex2 already is (i, j, g). */
static int clash(int ex1, int ex2, int i, int j, int g) {
    for (int s = 0; s < nd; s++) {
        if (s == ex1 || s == ex2 || dG[s] < 0) continue;
        if (dI[s] == i && dJ[s] == j && dG[s] == g) return 1;
    }
    return 0;
}

static int init_darts(void) {
    nd = P_ * d;
    V_ = 2 * P_ * N_;
    for (int t = 0; t < nd; t++) dG[t] = -1;
    for (int l = 0; l < d; l++) {
        int perm[MAXP];
        for (int i = 0; i < P_; i++) perm[i] = i;
        for (int i = P_ - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
        }
        for (int i = 0; i < P_; i++) { dI[i * d + l] = i; dJ[i * d + l] = perm[i]; }
    }
    for (int t = 0; t < nd; t++) {
        int ok = 0;
        for (int tries = 0; tries < 5000 && !ok; tries++) {
            int g = rndint(N_);
            if (!clash(t, -1, dI[t], dJ[t], g)) { dG[t] = g; ok = 1; }
        }
        if (!ok) return 0;
    }
    return 1;
}

/* Simulated annealing with a time-based temperature schedule. Returns final cost. */
static long anneal(double until, double slice) {
    const double T0 = 4.0, T1 = 0.25;
    double start = now();
    long cost = lift_cost();
    while (cost > 0) {
        double tn = now();
        if (tn >= until || tn >= t_end) break;
        double frac = (tn - start) / slice;
        if (frac > 1.0) frac = 1.0;
        double T = T0 * pow(T1 / T0, frac);
        if (P_ == 1 || rndint(2) == 0) {
            int t = rndint(nd);
            int g = rndint(N_);
            if (g == dG[t] || clash(t, -1, dI[t], dJ[t], g)) continue;
            int old = dG[t];
            dG[t] = g;
            long nc = lift_cost();
            long delta = nc - cost;
            if (delta <= 0 || rnd01() < exp(-(double)delta / T)) cost = nc;
            else dG[t] = old;
        } else {
            int t1 = rndint(nd), t2 = rndint(nd);
            if (dJ[t1] == dJ[t2]) continue;
            if (clash(t1, t2, dI[t1], dJ[t2], dG[t1]) ||
                clash(t1, t2, dI[t2], dJ[t1], dG[t2])) continue;
            int s = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = s;
            long nc = lift_cost();
            long delta = nc - cost;
            if (delta <= 0 || rnd01() < exp(-(double)delta / T)) cost = nc;
            else { s = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = s; }
        }
    }
    return cost;
}

static void graph_from_lift(Graph *g) {
    build_nbr();
    g->n = V_;
    for (int v = 0; v < V_; v++) {
        g->deg[v] = d;
        g->side[v] = (unsigned char)(v >= P_ * N_);
        for (int k = 0; k < d; k++) g->adj[v][k] = nbr[v][k];
    }
}

static Graph best, cand;

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    if (d < 1 || d > MAXD || D < 1) { printf("0 0\n"); return 0; }
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    if (d >= 2 && D >= 2) {
        long inc = 1;
        while (now() < t_end) {
            long mb = moore_bound();
            if (best.n + 2 > mb || best.n + 2 > MAXV) break;
            int P = 1 + rndint(5);
            long N = best.n / (2 * P) + inc;
            if (N < 2 || 2L * P * N > MAXV || N > MAXG) { inc = 1; continue; }
            if (!build_group((int)N)) continue;
            P_ = P;
            N_ = (int)N;
            if (!init_darts()) continue;
            double rem = t_end - now();
            if (rem <= 0) break;
            double slice = rem / 6.0;
            if (slice < 2.0) slice = rem;
            if (slice > 12.0) slice = 12.0;
            long c = anneal(now() + slice, slice);
            if (c == 0) {
                graph_from_lift(&cand);
                if (cand.n > best.n && is_valid(&cand)) copy_graph(&best, &cand);
                inc *= 2;
                if (inc > 4096) inc = 4096;
            } else {
                inc /= 2;
                if (inc < 1) inc = 1;
            }
        }
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    usable = max(1.0, 0.85 * time_limit - 2.0)
    end = t0 + usable

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Replace the current best if (n, e) is a larger valid graph."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            ar = lib.araujo_lopez_graph(d - 2)
            consider(ar[0], ar[1])
        except (ValueError, RuntimeError):
            pass
    if D == 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    if D >= 2 and 2 <= d <= 32:
        c_budget = end - time.monotonic() - 2.0
        if c_budget > 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                                 stdin_graph=best, timeout=c_budget + 8)
                out = lib.parse_graph_text(text)
                consider(out[0], out[1])
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
