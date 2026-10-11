import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Structured bases (kept from the parent).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Points are all points of PG(3, q); lines are totally isotropic lines of the
    symplectic form B(x, y) = x0*y1 - x1*y0 + x2*y3 - x3*y2. Degree is q + 1,
    diameter is 4, and the order is 2(q+1)(q^2+1).
    """
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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# C engine: bitset-guided insertion + annealed repair.
#
# New in this version: the insertion step chooses the newcomer's neighbourhood
# by greedy set cover of the radius-(D-1) balls (a vertex s covers u exactly when
# dist(s, u) <= D-1), so the new vertex is placed where it fixes the most bad
# pairs. Slots are freed by stealing an edge from a full neighbour when needed.
# Then a simulated annealer with degree-preserving bipartite double-edge
# switches drives the number of bad pairs (distance > D) to zero. Every accepted
# graph has cost 0 and is saved as the new anchor; failed attempts restart from
# the anchor. Bipartiteness is preserved by all moves.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define CAP 4096
#define MAXDEG 64
#define WMAX (CAP / 64)

typedef uint64_t u64;

static int d_, D_, moore_;
static int n_;
static int deg_[CAP];
static int adj_[CAP * MAXDEG];
static int col_[CAP];
static u64 bufA[CAP * WMAX];
static u64 bufB[CAP * WMAX];

static int bN_;
static int bDeg_[CAP];
static int bAdj_[CAP * MAXDEG];
static int bCol_[CAP];

#define A(v, i) adj_[(v) * MAXDEG + (i)]

static u64 rs_ = 88172645463325252ULL;
static u64 rnd64(void) {
    rs_ ^= rs_ >> 12; rs_ ^= rs_ << 25; rs_ ^= rs_ >> 27;
    return rs_ * 2685821657736338717ULL;
}
static unsigned rnd_u(void) { return (unsigned)(rnd64() >> 33); }
static double urand(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static clock_t c0_;
static time_t w0_;
static double budget_;

static int timeup(void) {
    if ((double)(clock() - c0_) / CLOCKS_PER_SEC >= budget_) return 1;
    return difftime(time(NULL), w0_) >= budget_;
}

static int has_edge(int x, int y) {
    for (int i = 0; i < deg_[x]; i++) if (A(x, i) == y) return 1;
    return 0;
}
static void repl(int x, int old, int nw) {
    for (int i = 0; i < deg_[x]; i++) if (A(x, i) == old) { A(x, i) = nw; return; }
}
static void rm_from(int x, int y) {
    for (int i = 0; i < deg_[x]; i++) if (A(x, i) == y) {
        A(x, i) = A(x, deg_[x] - 1);
        deg_[x]--;
        return;
    }
}
static void add_edge(int x, int y) {
    A(x, deg_[x]) = y; deg_[x]++;
    A(y, deg_[y]) = x; deg_[y]++;
}

/* Balls of radius R as bitsets; result is returned in whichever buffer holds it. */
static u64 *balls(int R, u64 *X, u64 *Y) {
    int n = n_, Wc = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        u64 *x = X + (size_t)v * Wc;
        for (int w = 0; w < Wc; w++) x[w] = 0;
        x[v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < R; r++) {
        for (int v = 0; v < n; v++) {
            u64 *y = Y + (size_t)v * Wc;
            const u64 *x = X + (size_t)v * Wc;
            for (int w = 0; w < Wc; w++) y[w] = x[w];
            for (int i = 0; i < deg_[v]; i++) {
                const u64 *z = X + (size_t)A(v, i) * Wc;
                for (int w = 0; w < Wc; w++) y[w] |= z[w];
            }
        }
        u64 *t = X; X = Y; Y = t;
    }
    return X;
}

static long long bad_pairs(void) {
    int n = n_, Wc = (n + 63) >> 6;
    u64 *r = balls(D_, bufA, bufB);
    long long tot = 0;
    for (int v = 0; v < n; v++) {
        int cnt = 0;
        const u64 *x = r + (size_t)v * Wc;
        for (int w = 0; w < Wc; w++) cnt += __builtin_popcountll(x[w]);
        tot += n - cnt;
    }
    return tot / 2;
}

/* Insert a new vertex on side c, joined to a greedy cover chosen by (D-1)-ball gain. */
static void insert_vertex(int c) {
    int n = n_, Wc = (n + 63) >> 6;
    u64 *r1 = balls(D_ - 1, bufA, bufB);
    u64 U[WMAX];
    for (int w = 0; w < Wc; w++) U[w] = ~0ULL;
    if (n & 63) U[Wc - 1] = (1ULL << (n & 63)) - 1;
    static int taken[CAP];
    for (int v = 0; v < n; v++) taken[v] = 0;
    int chosen[MAXDEG], nch = 0;
    for (int k = 0; k < d_; k++) {
        int best = -1;
        double bs = -1e18;
        for (int s = 0; s < n; s++) {
            if (col_[s] != 1 - c || taken[s]) continue;
            int g = 0;
            const u64 *x = r1 + (size_t)s * Wc;
            for (int w = 0; w < Wc; w++) g += __builtin_popcountll(x[w] & U[w]);
            double sc = g + 0.9 * urand() - (deg_[s] >= d_ ? 0.5 : 0.0);
            if (sc > bs) { bs = sc; best = s; }
        }
        if (best < 0) break;
        taken[best] = 1;
        chosen[nch++] = best;
        const u64 *x = r1 + (size_t)best * Wc;
        for (int w = 0; w < Wc; w++) U[w] &= ~x[w];
    }
    int v = n_++;
    col_[v] = c;
    deg_[v] = 0;
    for (int k = 0; k < nch; k++) {
        int s = chosen[k];
        if (deg_[s] >= d_) {
            int t = A(s, rnd_u() % deg_[s]);
            rm_from(s, t);
            rm_from(t, s);
        }
        add_edge(s, v);
    }
}

/* Add cross-side edges between deficient vertices (only shortens distances). */
static void fill(void) {
    int n = n_;
    if (n == 0) return;
    int off = (int)(rnd_u() % n);
    for (int ii = 0; ii < n; ii++) {
        int a = (ii + off) % n;
        if (col_[a] != 0 || deg_[a] >= d_) continue;
        for (int jj = 0; jj < n && deg_[a] < d_; jj++) {
            int b = (jj + off) % n;
            if (col_[b] != 1 || deg_[b] >= d_ || has_edge(a, b)) continue;
            add_edge(a, b);
        }
    }
}

static int pick_side(int side) {
    for (int t = 0; t < 64; t++) {
        int v = (int)(rnd_u() % n_);
        if (col_[v] == side && deg_[v] > 0) return v;
    }
    return -1;
}

/* Degree-preserving bipartite switches minimising bad pairs. Returns final cost. */
static long long anneal(long long L, double T0, double T1) {
    long long cur = bad_pairs();
    for (long long it = 0; it < L && cur > 0; it++) {
        if ((it & 255) == 0 && timeup()) break;
        double T = T0 + (T1 - T0) * (double)it / (double)L;
        int a = pick_side(0), c = pick_side(0);
        if (a < 0 || c < 0 || a == c) continue;
        int b = A(a, rnd_u() % deg_[a]);
        int e = A(c, rnd_u() % deg_[c]);
        if (has_edge(a, e) || has_edge(c, b)) continue;
        /* a-b, c-e  ->  a-e, c-b */
        repl(a, b, e); repl(b, a, c); repl(e, c, a); repl(c, e, b);
        long long nw = bad_pairs();
        if (nw <= cur || urand() < exp(-(double)(nw - cur) / T)) {
            cur = nw;
        } else {
            repl(a, e, b); repl(e, a, c); repl(c, b, e); repl(b, c, a);
        }
    }
    return cur;
}

static void save_best(void) {
    bN_ = n_;
    memcpy(bDeg_, deg_, sizeof(int) * n_);
    memcpy(bAdj_, adj_, sizeof(int) * MAXDEG * n_);
    memcpy(bCol_, col_, sizeof(int) * n_);
}

static void load_best(void) {
    n_ = bN_;
    memcpy(deg_, bDeg_, sizeof(int) * n_);
    memcpy(adj_, bAdj_, sizeof(int) * MAXDEG * n_);
    memcpy(col_, bCol_, sizeof(int) * n_);
}

static void fail_out(void) {
    printf("0 0\n");
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    budget_ = atof(argv[4]);
    moore_ = argc >= 6 ? atoi(argv[5]) : CAP;
    rs_ ^= seed * 0x9E3779B97F4A7C15ULL + 1;
    if (rs_ == 0) rs_ = 1;
    for (int i = 0; i < 10; i++) rnd64();
    c0_ = clock();
    w0_ = time(NULL);

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { fail_out(); return 0; }
    if (d_ < 1 || d_ >= MAXDEG || D_ < 2 || n <= 0 || n > CAP - 2 || m < 0) { fail_out(); return 0; }
    int *eu = malloc(sizeof(int) * (m > 0 ? m : 1));
    int *ev = malloc(sizeof(int) * (m > 0 ? m : 1));
    if (!eu || !ev) { fail_out(); return 0; }
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) { fail_out(); return 0; }
    }

    n_ = n;
    for (int v = 0; v < n; v++) { deg_[v] = 0; col_[v] = -1; }
    for (int i = 0; i < m; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) { fail_out(); return 0; }
        if (has_edge(u, v) || deg_[u] >= d_ || deg_[v] >= d_) { fail_out(); return 0; }
        add_edge(u, v);
    }
    /* Bipartition check. */
    int *q = malloc(sizeof(int) * CAP);
    for (int s = 0; s < n; s++) {
        if (col_[s] >= 0) continue;
        col_[s] = 0;
        int head = 0, tail = 0;
        q[tail++] = s;
        while (head < tail) {
            int u = q[head++];
            for (int i = 0; i < deg_[u]; i++) {
                int w = A(u, i);
                if (col_[w] < 0) { col_[w] = 1 - col_[u]; q[tail++] = w; }
                else if (col_[w] == col_[u]) { fail_out(); return 0; }
            }
        }
    }
    free(q);

    save_best();
    while (!timeup()) {
        if (moore_ > 0 && n_ >= moore_) break;
        if (n_ >= CAP - 2) break;
        load_best();
        insert_vertex((int)(rnd_u() & 1));
        fill();
        long long L = 3000 + (long long)(rnd_u() % 20000);
        double T0 = 0.25 + 0.9 * urand();
        long long cost = anneal(L, T0, 0.03);
        if (cost == 0) save_best();
    }

    long long tot = 0;
    for (int v = 0; v < bN_; v++) tot += bDeg_[v];
    printf("%d %lld\n", bN_, tot / 2);
    for (int u = 0; u < bN_; u++) {
        for (int i = 0; i < bDeg_[u]; i++) {
            int v = bAdj_[u * MAXDEG + i];
            if (u < v) printf("%d %d\n", u, v);
        }
    }
    free(eu);
    free(ev);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python glue.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Structured base: generalized quadrangle for D >= 4, projective plane for D = 3.
    base = None
    if D >= 4:
        base = _best_gq(d)
    elif D == 3:
        base = _best_pg(d)
    if base is not None:
        consider(*base)
    base_n, base_e = best_n, list(best_e)

    # Hand the base to the C engine, which inserts vertices and repairs by annealing.
    moore = lib.moore_bound(d, D)
    if D >= 2 and d <= 60 and best_n < moore:
        elapsed = time.monotonic() - start
        budget = 0.75 * time_limit - elapsed - 2.0
        if budget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", moore],
                                stdin_graph=(base_n, base_e), timeout=budget + 8.0)
                n2, e2 = lib.parse_graph_text(out)
                consider(n2, e2)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
