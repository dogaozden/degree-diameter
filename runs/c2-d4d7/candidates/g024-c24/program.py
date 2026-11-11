"""Bold variant: multi-fibre voltage lifts found by simulated annealing, with no cover or grow stages.

Construction change from the parent:
- The parent mixes Z_k covers, PSL/PGL lifts, and grow-by-two. This program uses only one engine:
  a regular voltage lift of a random d-regular bipartite base on p + p fibres (p in 1..4), over a
  random group of order N (cyclic, or Z_m x|_r Z_k). Each attempt anneals the voltages directly.
- Vertex transitivity within each fibre means the diameter check needs only 2p BFS sources.
- Each success sets the next target, so the order ratchets upward from the current best.

Risk: the parent's Z_k-cover and grow stages are gone. If no lift beats the start graph, the
d=4 D=7 case returns H(3) with 728 vertices, which is below the 840 record. The program is untested.
Validity is still enforced: C checks every output with a full bitset check, and Python checks
the output again with lib.is_valid and keeps the best valid graph.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-fibre voltage-lift annealer.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * A lift has p fibres per side, each of size N, over a group G of order N.
 * Base: a random d-regular bipartite multigraph on p+p nodes. Dart (i,j,g) joins
 * (A,i,x) to (B,j,x*g) for all x. Left multiplication by any h is an automorphism,
 * so the diameter check needs BFS only from the 2p fibre-identity vertices.
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
#define MAXG 1200
#define MAXP 4
#define MAXDART (MAXD * MAXP)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static Graph best;

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
    if (b < 0) b += m;
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

/* Number of unordered pairs at distance > D (bitset BFS). */
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

/* ---------------------------------------------------------------- groups
 * Multiplication table GT[x*GN + y], identity 0, inverses GINV. */
static int GN;
static int GT[MAXG * MAXG];
static int GINV[MAXG];
static int RP[MAXG];

/* Random group of order N: Z_m x|_r Z_k with m*k = N, element a*k+b. r=1 gives the direct product. */
static int make_group(int N) {
    for (int tries = 0; tries < 64; tries++) {
        int divs[64], nd = 0;
        for (int m = 1; m <= N && nd < 64; m++)
            if (N % m == 0) divs[nd++] = m;
        int m = divs[rndint(nd)];
        int k = N / m;
        int r = 0;
        if (m > 1) r = 1 + rndint(m - 1);
        if (m > 1 && (gcd(r, m) != 1 || powmod(r, k, m) != 1 % m)) continue;
        RP[0] = 1 % m;
        for (int b = 1; b < k; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
        GN = N;
        for (int x = 0; x < N; x++) {
            int a = x / k, b = x % k;
            for (int y = 0; y < N; y++) {
                int c = y / k, e = y % k;
                GT[x * N + y] = (int)(((a + (long)RP[b] * c) % m) * k + (b + e) % k);
            }
        }
        for (int x = 0; x < N; x++)
            for (int y = 0; y < N; y++)
                if (GT[x * N + y] == 0) { GINV[x] = y; break; }
        return 1;
    }
    return 0;
}

/* ---------------------------------------------------------------- lifts */
static int di[MAXDART], dj[MAXDART], dg[MAXDART], bestdg[MAXDART];

/* Random d-regular bipartite multigraph on p+p nodes, connected. M[i][j] = number of darts i->j. */
static int make_base(int p, int M[MAXP][MAXP]) {
    for (int tries = 0; tries < 200; tries++) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
            }
            for (int i = 0; i < p; i++) M[i][perm[i]]++;
        }
        int seen[2 * MAXP] = {0}, stack[2 * MAXP], top = 0, nseen = 1;
        seen[0] = 1;
        stack[top++] = 0;
        while (top) {
            int v = stack[--top];
            for (int u = 0; u < 2 * p; u++) {
                if (seen[u]) continue;
                int linked = v < p ? (u >= p && M[v][u - p]) : (u < p && M[u][v - p]);
                if (linked) { seen[u] = 1; nseen++; stack[top++] = u; }
            }
        }
        if (nseen == 2 * p) return 1;
    }
    return 0;
}

/* A fresh voltage for dart t that differs from the other darts on the same (i,j) pair. */
static int fresh_g(int t, int nd) {
    int N = GN;
    for (;;) {
        int g = rndint(N), ok = 1;
        for (int s = 0; s < nd && ok; s++)
            if (s != t && di[s] == di[t] && dj[s] == dj[t] && dg[s] == g) ok = 0;
        if (ok) return g;
    }
}

/* Vertex layout: A-fibre i, element x -> i*N + x; B-fibre j, element x -> (p+j)*N + x. */
static void build_lift(Graph *g, int p, int nd) {
    int N = GN;
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, di[t] * N + x, (p + dj[t]) * N + GT[x * N + dg[t]]);
}

static int dq[MAXN], qq[MAXN];

/* Unreached (representative, vertex) pairs at distance > D, summed over the 2p representatives. */
static long lift_cost(const Graph *g, int p) {
    int nv = g->n, N = GN;
    long total = 0;
    for (int b = 0; b < 2 * p; b++) {
        int src = b * N;
        for (int v = 0; v < nv; v++) dq[v] = -1;
        int head = 0, tail = 0;
        dq[src] = 0;
        qq[tail++] = src;
        while (head < tail) {
            int v = qq[head++];
            if (dq[v] >= D) continue;
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (dq[u] < 0) {
                    dq[u] = dq[v] + 1;
                    qq[tail++] = u;
                }
            }
        }
        total += nv - tail;
    }
    return total;
}

static Graph cand;

/* One annealing attempt on a random base over the current group. Returns 1 and a verified graph on success. */
static int attempt(int p, double until, long steps, Graph *out) {
    int M[MAXP][MAXP];
    int N = GN;
    if (N < d) return 0;
    if (!make_base(p, M)) return 0;
    int nd = 0;
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                di[nd] = i;
                dj[nd] = j;
                dg[nd] = 0;
                nd++;
            }
    for (int t = 0; t < nd; t++) dg[t] = fresh_g(t, nd);
    build_lift(&cand, p, nd);
    long bad = lift_cost(&cand, p);
    long bestbad = bad;
    memcpy(bestdg, dg, sizeof(int) * nd);
    double T0 = 1.0 + 0.05 * (double)bad;
    for (long s = 0; s < steps && bad > 0; s++) {
        if ((s & 127) == 0 && now() > until) break;
        double T = T0 * (1.0 - (double)s / (double)steps) + 0.02;
        int t = rndint(nd);
        int old = dg[t];
        dg[t] = fresh_g(t, nd);
        build_lift(&cand, p, nd);
        long nb = lift_cost(&cand, p);
        if (nb <= bad || rnd01() < exp(-(double)(nb - bad) / T)) {
            bad = nb;
            if (bad < bestbad) {
                bestbad = bad;
                memcpy(bestdg, dg, sizeof(int) * nd);
            }
        } else {
            dg[t] = old;
        }
    }
    if (bestbad != 0) return 0;
    memcpy(dg, bestdg, sizeof(int) * nd);
    build_lift(&cand, p, nd);
    if (!is_valid(&cand)) return 0;
    copy_graph(out, &cand);
    return 1;
}

/* Ratchet: keep finding lifts strictly larger than the current best. */
static void grow_lifts(double until) {
    static Graph out;
    long cap = moore_bound();
    if (cap > MAXN) cap = MAXN;
    static const int ps[8] = {1, 1, 1, 1, 2, 2, 3, 4};
    while (now() < until) {
        if (best.n + 1 > cap) return;
        int p = ps[rndint(8)];
        long Nmin = best.n / (2 * p) + 1;
        long Nmax = cap / (2 * p);
        if (Nmax > MAXG) Nmax = MAXG;
        if (Nmin > Nmax) continue;
        long N = Nmin + rndint(3);
        if (N > Nmax) N = Nmax;
        if (N < d) N = d;
        if (N > Nmax) continue;
        if (2L * p * N <= best.n) continue;
        if (!make_group((int)N)) continue;
        double slice = now() + 2.5;
        if (slice > until) slice = until;
        if (attempt(p, slice, 150000, &out) && out.n > best.n && is_valid(&out))
            copy_graph(&best, &out);
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
    double t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 2 || d > 31) {
        if (d >= 1 && d <= 31) complete_bipartite(&best);
        else best.n = 0;
        if (best.n > 0) print_graph(&best);
        else printf("0 0\n");
        return 0;
    }

    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (best.n < moore_bound()) grow_lifts(t_end);
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


def _gh_h3():
    """Incidence graph of the split Cayley hexagon H(3): 364 + 364 vertices, degree 4, diameter 6.

    Returns None if no sign convention verifies with lib.is_valid.
    """
    q = 3

    def norm(v):
        c = next(x for x in v if x)
        inv = 1 if c == 1 else 2
        return tuple((x * inv) % q for x in v)

    vecs = itertools.product(range(q), repeat=7)
    pts = sorted({norm(v) for v in vecs if any(v) and
                  (v[0] * v[4] + v[1] * v[5] + v[2] * v[6] - v[3] * v[3]) % q == 0})
    P = len(pts)
    index = {p: i for i, p in enumerate(pts)}

    def bil(x, y):
        return (x[0] * y[4] + x[4] * y[0] + x[1] * y[5] + x[5] * y[1] +
                x[2] * y[6] + x[6] * y[2] + x[3] * y[3]) % q

    def pl(x, y, i, j):
        return (x[i] * y[j] - x[j] * y[i]) % q

    conds = [((1, 2), (3, 4)), ((5, 4), (3, 2)), ((2, 0), (3, 5)),
             ((6, 5), (3, 0)), ((0, 1), (3, 6)), ((4, 6), (3, 1))]
    combos = ((1, 0), (0, 1), (1, 1), (1, 2))
    for s in (1, -1):
        lines = set()
        for i in range(P):
            x = pts[i]
            for j in range(i + 1, P):
                y = pts[j]
                if bil(x, y):
                    continue
                if any((pl(x, y, *a) - s * pl(x, y, *b)) % q for a, b in conds):
                    continue
                L = frozenset(index[norm(tuple((a * x[k] + b * y[k]) % q for k in range(7)))]
                              for a, b in combos)
                lines.add(L)
        if len(lines) != P or any(len(L) != 4 for L in lines):
            continue
        ordered = sorted(lines, key=sorted)
        edges = [(p, P + j) for j, L in enumerate(ordered) for p in L]
        n = P + len(ordered)
        if lib.is_valid(n, edges, 4, 6):
            return n, edges
    return None


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
    if d == 4 and D >= 6:
        try:
            gh = _gh_h3()
        except Exception:
            gh = None
        if gh is not None:
            out.append(gh)
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

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
    if budget <= 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 6)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
