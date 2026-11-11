"""Bold variant: bi-Cayley and Cayley graphs over PGL(2,q), q prime, instead of metacyclic lifts.

The parent searched only metacyclic voltage lifts. The record order 2184 equals |PGL(2,13)|, so this
variant samples non-metacyclic groups directly:
  * Cayley graph of PGL(2,q) with an odd generating set (bipartite by the square class of det),
    order |PGL(2,q)|, checked with one BFS from the identity (vertex-transitive).
  * bi-Cayley graph over PGL(2,q) with 2|PGL(2,q)| vertices, checked with BFS from both fibre identities.
Candidates are validated with lib.is_valid before use. The parent's W(q) / AL / PG starts remain the
fallback, and the C engine still grows the best graph found.
"""
import itertools
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

static int d, D;
static long MOORE;
static long target_n = 0;
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
/* Reachability balls (within D) of the most recent bad_pairs call. */
static uint64_t *balls_now = NULL;

/* Number of unordered pairs at distance > D (bitset ball expansion). */
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
    balls_now = cur;
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

/* Metacyclic group Z_m x|_r Z_k, element a*k+b, (a,b)(c,e) = (a + r^b c, b + e). */
typedef struct {
    int m, k, r;
    int rp[MAXN];
} Grp;

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

static void set_group(Grp *G, int m, int k, int r) {
    G->m = m; G->k = k; G->r = r;
    G->rp[0] = 1 % m;
    for (int b = 1; b < k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * r % m);
}

/* Uniformly random metacyclic group of order N (reservoir sampling over all (m, r)). */
static int pick_group(int N, Grp *G) {
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
    set_group(G, bm, bk, br);
    return 1;
}

/* Base multigraph on p + p vertices, d-regular: d random permutations, one dart per fibre each. */
static int di[MAXDART], dj[MAXDART], dg[MAXDART];

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

/* True if voltage g on dart t would duplicate another dart's voltage on the same fibre pair. */
static int clashes(int t, int g, int nd) {
    for (int s = 0; s < nd; s++)
        if (s != t && di[s] == di[t] && dj[s] == dj[t] && dg[s] == g) return 1;
    return 0;
}

/* Vertices: A-fibre i element x -> i*N + x; B-fibre j element x -> (p+j)*N + x. */
static void build_lift(Graph *g, int p, int N, const Grp *G, int nd) {
    int S = p * N;
    g->n = 2 * S;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= S; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, di[t] * N + x, S + dj[t] * N + gmul(G, x, dg[t]));
}

static int dist_buf[MAXN], queue_buf[MAXN];

/* Left multiplication is an automorphism acting regularly on each fibre, so the diameter is at
 * most D iff BFS from the identity of every fibre (2p sources) reaches everything within D. */
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

/* Anneal the voltages of the current darts; leaves dg and g consistent with the result. */
static long anneal(Graph *g, int p, int N, const Grp *G, int nd, int maxit, double until) {
    build_lift(g, p, N, G, nd);
    long bad = orbit_bad(g, p, N);
    double T = 1.0;
    for (int it = 0; it < maxit && bad > 0; it++) {
        if ((it & 63) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = dg[t];
        int ng = rndint(N);
        if (ng == old || clashes(t, ng, nd)) continue;
        dg[t] = ng;
        build_lift(g, p, N, G, nd);
        long nb = orbit_bad(g, p, N);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
        else dg[t] = old;
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    build_lift(g, p, N, G, nd);
    return bad;
}

/* Repeated random group / base / annealing tries at order N until the slice ends. */
static int attempt_order(Graph *best, int p, int N, double until) {
    static Graph cand;
    static Grp G;
    if (N < d) return 0;
    int nd = p * d;
    while (now() < until) {
        if (!pick_group(N, &G)) return 0;
        make_darts(p);
        for (int t = 0; t < nd; t++) dg[t] = -1;
        for (int t = 0; t < nd; t++) {
            int g;
            do { g = rndint(N); } while (clashes(t, g, nd));
            dg[t] = g;
        }
        long bad = anneal(&cand, p, N, &G, nd, 6000, until);
        if (bad == 0 && cand.n > best->n && is_valid(&cand)) {
            copy_graph(best, &cand);
            return 1;
        }
    }
    return 0;
}

/* Search: adaptive step climbing from the current best, plus (when a record is known) direct
 * attempts at the record order ceil(target / 2p) per fibre. Only adaptive attempts move the step. */
static void search(Graph *best, double until) {
    long step = 1;
    while (now() < until) {
        if (best->n + 2 > MOORE) return;
        int p = rndint(3) == 0 ? 2 : 1;
        long N = 0;
        int use_target = (target_n > best->n) && (rndint(2) == 0);
        if (use_target) {
            N = (target_n + 2L * p - 1) / (2L * p);
            if (!(2L * p * N <= MOORE && 2L * p * N <= MAXN)) use_target = 0;
        }
        if (!use_target) {
            for (;;) {
                long S = best->n / 2 + step;
                N = (S + p - 1) / p;
                if (N < d) N = d;
                if (2L * p * N <= MOORE && 2L * p * N <= MAXN) break;
                if (p == 2) { p = 1; continue; }
                if (step > 1) { step = 1; continue; }
                return;
            }
        }
        double left = until - now();
        double sl = left / 8;
        if (sl < 0.5) sl = 0.5;
        if (sl > 3.0) sl = 3.0;
        if (sl > left) sl = left;
        int ok = attempt_order(best, p, (int)N, now() + sl);
        if (!use_target) {
            if (ok) { if (step < 512) step *= 2; }
            else if (step > 1) step /= 2;
        }
    }
}

/* Final phase: insert one vertex per side, then repair with bad-pair-directed 2-switches. */
static int grow_once(const Graph *best, Graph *work, double until) {
    int n = best->n;
    if (n + 2 > MOORE || n + 2 > MAXN) return 0;
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
    int W = (work->n + 63) / 64;
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        int v = rndint(work->n);
        for (int tries = 0; tries < 30 && badv[v] == 0; tries++) v = rndint(work->n);
        if (work->deg[v] == 0) continue;
        int u = work->adj[v][rndint(work->deg[v])];
        int s = -1;
        /* Directed choice: partner on v's side that v cannot currently reach within D. */
        if (badv[v] > 0 && rndint(4) != 0) {
            for (int tr = 0; tr < 40; tr++) {
                int c = rndint(work->n);
                if (c == v || work->side[c] != work->side[v] || work->deg[c] == 0) continue;
                if (!((balls_now[(size_t)v * W + c / 64] >> (c % 64)) & 1ULL)) { s = c; break; }
            }
        }
        if (s < 0) {
            s = rndint(work->n);
            if (work->side[s] != work->side[v] || s == v || work->deg[s] == 0) continue;
        }
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
    while (now() < until && best->n + 2 <= MOORE) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice)) copy_graph(best, &work);
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

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    MOORE = moore_bound();
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    if (D >= 2 && best.n < MOORE) {
        search(&best, t0 + (t_end - t0) * 0.85);
    }
    if (best.n + 2 <= MOORE) grow_search(&best, t_end);
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


# ------------------------------------------------ PGL(2,q) group constructions

def _is_prime(q):
    return q >= 2 and all(q % p for p in range(2, int(q ** 0.5) + 1))


def _norm4(t, q):
    """Scale a 2x2 matrix (flattened) so its first nonzero entry is 1 (projective normal form)."""
    for c in t:
        if c:
            inv = pow(c, q - 2, q)
            return tuple(x * inv % q for x in t)
    raise ValueError("zero matrix")


def _mat_mul(x, y, q):
    a, b, c, d = x
    e, f, g, h = y
    return _norm4(((a * e + b * g) % q, (a * f + b * h) % q,
                   (c * e + d * g) % q, (c * f + d * h) % q), q)


class _PGL:
    """PGL(2,q) for prime q. Elements are normalized 2x2 matrices, indexed 0..N-1."""

    def __init__(self, q):
        self.q = q
        els = set()
        for t in itertools.product(range(q), repeat=4):
            if (t[0] * t[3] - t[1] * t[2]) % q:
                els.add(_norm4(t, q))
        self.els = sorted(els)
        self.N = len(self.els)
        self.idx = {e: i for i, e in enumerate(self.els)}
        self.ident = self.idx[(1, 0, 0, 1)]
        # Odd elements (non-square determinant) form the non-PSL coset: they flip the bipartition.
        self.odd = []
        for e in self.els:
            det = (e[0] * e[3] - e[1] * e[2]) % q
            self.odd.append(pow(det, (q - 1) // 2, q) != 1)
        self.odd_idx = [i for i in range(self.N) if self.odd[i]]
        self._perms = {}

    def inv(self, s):
        a, b, c, d = self.els[s]
        q = self.q
        return self.idx[_norm4((d, (-b) % q, (-c) % q, a), q)]

    def perm(self, s):
        """Right multiplication by element s: x -> x*s, as a list of indices."""
        p = self._perms.get(s)
        if p is None:
            if len(self._perms) > 96:
                self._perms.clear()
            es = self.els[s]
            q = self.q
            p = [self.idx[_mat_mul(e, es, q)] for e in self.els]
            self._perms[s] = p
        return p


def _reach(adj, n, src, D):
    """Number of vertices within distance D of src (BFS)."""
    seen_flag = [False] * n
    seen_flag[src] = True
    frontier = [src]
    seen = 1
    for _ in range(D):
        nxt = []
        for v in frontier:
            for u in adj[v]:
                if not seen_flag[u]:
                    seen_flag[u] = True
                    nxt.append(u)
        if not nxt:
            break
        seen += len(nxt)
        frontier = nxt
    return seen


def _random_cayley_set(G, d, rng):
    """Inverse-closed set of d odd group elements (indices), or None."""
    S = []
    for _ in range(64):
        if len(S) == d:
            break
        s = rng.choice(G.odd_idx)
        t = G.inv(s)
        new = [s] if t == s else [s, t]
        if len(S) + len(new) > d or any(x in S for x in new):
            continue
        S.extend(new)
    return S if len(S) == d else None


def _cayley_trial(G, d, D, rng):
    """Random Cayley graph of G with odd generators: order N, bipartite. Returns (n, edges) or None."""
    S = _random_cayley_set(G, d, rng)
    if S is None:
        return None
    N = G.N
    perms = [G.perm(s) for s in S]
    adj = [[p[x] for p in perms] for x in range(N)]
    if _reach(adj, N, G.ident, D) < N:
        return None
    edges = sorted({(min(x, y), max(x, y)) for x in range(N) for y in adj[x]})
    return N, edges


def _bicayley_trial(G, d, D, rng):
    """Random bi-Cayley graph over G with 2 fibres: A_x ~ B_{x s}. Returns (2N, edges) or None."""
    N = G.N
    S = rng.sample(range(N), d)
    fwd = [G.perm(s) for s in S]
    bwd = [G.perm(G.inv(s)) for s in S]
    n2 = 2 * N
    adj = [None] * n2
    for x in range(N):
        adj[x] = [N + p[x] for p in fwd]
    for y in range(N):
        adj[N + y] = [p[y] for p in bwd]
    if _reach(adj, n2, 0, D) < n2 or _reach(adj, n2, N, D) < n2:
        return None
    edges = [(x, N + p[x]) for x in range(N) for p in fwd]
    return n2, edges


def _family(d, D, best_n, deadline, seed):
    """Try PGL(2,q) Cayley and bi-Cayley candidates larger than best_n. Returns (n, edges) or None."""
    moore = lib.moore_bound(d, D)
    rng = random.Random(seed * 1000003 + d * 97 + D)
    tasks = []
    for q in range(3, 41):
        if not _is_prime(q):
            continue
        N = q * (q * q - 1)
        if N <= moore:
            tasks.append((N, "cay", q))
        if 2 * N <= moore:
            tasks.append((2 * N, "bi", q))
    tasks.sort(reverse=True)
    # Only sizes that are large relative to the Moore bound are worth the time.
    tasks = [t for t in tasks if t[0] > best_n and 4 * t[0] >= moore]
    groups = {}
    best = None
    for i, (n_task, kind, q) in enumerate(tasks):
        if n_task <= best_n:
            continue
        left = deadline - time.monotonic()
        if left <= 0.5:
            break
        slice_end = time.monotonic() + left / (len(tasks) - i)
        if q not in groups:
            groups[q] = _PGL(q)
        G = groups[q]
        trial = _cayley_trial if kind == "cay" else _bicayley_trial
        while time.monotonic() < slice_end:
            res = trial(G, d, D, rng)
            if res is None:
                continue
            n, edges = res
            if n > best_n and lib.is_valid(n, edges, d, D):
                best = (n, edges)
                best_n = n
                break
    return best


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

    # Non-metacyclic group phase (PGL(2,q) Cayley / bi-Cayley), a fraction of the time.
    if D >= 4 and d >= 3:
        try:
            got = _family(d, D, best[0], t0 + 0.4 * time_limit, seed)
            if got is not None and got[0] > best[0] and lib.is_valid(got[0], got[1], d, D):
                best = got
        except Exception:
            pass

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
