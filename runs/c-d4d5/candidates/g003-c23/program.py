import itertools
import math
import random
import time

import lib

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 512
#define MAXW (MAXN / 64)
#define MAXD 16
#define ATT 60000L

static int d_, D_, N;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static uint64_t BUFA[MAXN][MAXW];
static uint64_t BUFB[MAXN][MAXW];

static int best_N;
static int best_deg[MAXN];
static int best_adj[MAXN][MAXD];
static int best_col[MAXN];

static int lg_t[16], lg_u[16], lg_v[16], nlog;
static uint64_t rs = 88172645463325252ULL;
static double t_end;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now_s(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered vertex pairs at distance > D_ (zero iff valid). */
static long cost(void) {
    int W = (N + 63) / 64;
    uint64_t (*cu)[MAXW] = BUFA, (*nx)[MAXW] = BUFB;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W; w++) cu[v][w] = 0;
        cu[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) nx[v][w] = cu[v][w];
            for (int k = 0; k < deg[v]; k++) {
                int u = adj[v][k];
                for (int w = 0; w < W; w++) nx[v][w] |= cu[u][w];
            }
        }
        uint64_t (*tmp)[MAXW] = cu;
        cu = nx;
        nx = tmp;
    }
    long tot = 0;
    for (int v = 0; v < N; v++)
        for (int w = 0; w < W; w++) tot += popc(cu[v][w]);
    return ((long)N * N - tot) / 2;
}

static int has_edge(int u, int v) {
    for (int k = 0; k < deg[u]; k++) if (adj[u][k] == v) return 1;
    return 0;
}
static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}
static void del_one(int u, int v) {
    for (int k = 0; k < deg[u]; k++)
        if (adj[u][k] == v) { adj[u][k] = adj[u][--deg[u]]; break; }
}
static void del_edge(int u, int v) { del_one(u, v); del_one(v, u); }

static void op_add(int u, int v) {
    add_edge(u, v);
    lg_t[nlog] = 0; lg_u[nlog] = u; lg_v[nlog] = v; nlog++;
}
static void op_del(int u, int v) {
    del_edge(u, v);
    lg_t[nlog] = 1; lg_u[nlog] = u; lg_v[nlog] = v; nlog++;
}
static void undo(void) {
    while (nlog > 0) {
        nlog--;
        if (lg_t[nlog] == 0) del_edge(lg_u[nlog], lg_v[nlog]);
        else add_edge(lg_u[nlog], lg_v[nlog]);
    }
}

/* Random vertex with spare degree on colour c, or -1. */
static int pick_side(int c) {
    for (int t = 0; t < 40; t++) {
        int v = rndi(N);
        if (col[v] == c && deg[v] < d_) return v;
    }
    return -1;
}

/* Uniform-ish random edge, oriented so L has colour 0. */
static int rand_edge(int *L, int *R) {
    for (int t = 0; t < 60; t++) {
        int v = rndi(N);
        if (deg[v] == 0) continue;
        int w = adj[v][rndi(deg[v])];
        if (col[v] == 0) { *L = v; *R = w; } else { *L = w; *R = v; }
        return 1;
    }
    return 0;
}

/* Double-edge swap: (a,b),(c,e) -> (a,e),(c,b). Degrees preserved. */
static int move_swap(void) {
    int a, b, c, e;
    nlog = 0;
    if (!rand_edge(&a, &b) || !rand_edge(&c, &e)) return 0;
    if (a == c || b == e || has_edge(a, e) || has_edge(c, b)) return 0;
    op_del(a, b);
    op_del(c, e);
    op_add(a, e);
    op_add(c, b);
    return 1;
}

/* Delete one edge and add a new edge between spare-degree vertices. */
static int move_rewire(void) {
    int a, b;
    nlog = 0;
    if (!rand_edge(&a, &b)) return 0;
    op_del(a, b);
    int x = pick_side(0), y = pick_side(1);
    if (x < 0 || y < 0 || has_edge(x, y)) { undo(); return 0; }
    op_add(x, y);
    return 1;
}

static int anneal(long moves, double T0, double T1) {
    long cur = cost();
    if (cur == 0) return 1;
    for (long it = 0; it < moves; it++) {
        if ((it & 255) == 0 && now_s() > t_end) break;
        double T = T0 + (T1 - T0) * (double)it / (double)moves;
        if (rndu() < 0.2) {
            /* Fill move: adding an edge never increases the cost. */
            int x = pick_side(0), y = pick_side(1);
            if (x >= 0 && y >= 0 && !has_edge(x, y)) {
                add_edge(x, y);
                cur = cost();
                if (cur == 0) return 1;
            }
            continue;
        }
        int ok = (rndu() < 0.5) ? move_swap() : move_rewire();
        if (!ok) continue;
        long nc = cost();
        long delta = nc - cur;
        if (delta <= 0 || rndu() < exp(-(double)delta / T)) {
            cur = nc;
            nlog = 0;
            if (cur == 0) return 1;
        } else {
            undo();
        }
    }
    return cur == 0;
}

static long moore_cap(void) {
    long s = 0, p = 1;
    for (int i = 0; i < D_; i++) {
        s += p;
        p *= (d_ - 1);
        if (p > 1000000) p = 1000000;
    }
    return 2 * s;
}

static int grow2(long cap) {
    if (N + 2 > MAXN || (long)(N + 2) > cap) return 0;
    col[N] = 0; deg[N] = 0;
    col[N + 1] = 1; deg[N + 1] = 0;
    N += 2;
    return 1;
}

static void save_best(void) {
    best_N = N;
    for (int v = 0; v < N; v++) {
        best_deg[v] = deg[v];
        best_col[v] = col[v];
        memcpy(best_adj[v], adj[v], sizeof(adj[v]));
    }
}

static void restore_best(void) {
    N = best_N;
    for (int v = 0; v < N; v++) {
        deg[v] = best_deg[v];
        col[v] = best_col[v];
        memcpy(adj[v], best_adj[v], sizeof(adj[v]));
    }
}

static void reset_kdd(void) {
    N = 2 * d_;
    for (int v = 0; v < N; v++) { deg[v] = 0; col[v] = v < d_ ? 0 : 1; }
    for (int i = 0; i < d_; i++)
        for (int j = 0; j < d_; j++)
            add_edge(i, d_ + j);
}

static int colour_graph(void) {
    static int st[MAXN];
    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int sp = 0;
        st[sp++] = s;
        while (sp > 0) {
            int u = st[--sp];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (col[v] == -1) { col[v] = 1 - col[u]; st[sp++] = v; }
                else if (col[v] == col[u]) return 0;
            }
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    if (d_ < 2 || D_ < 2 || d_ > MAXD || 2 * d_ > MAXN) {
        printf("0 0\n");
        return 0;
    }
    rs ^= seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    t_end = now_s() + budget;
    long cap = moore_cap();

    int n = 0, m = 0, ok = 1;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n > 0 && n <= MAXN && m >= 0) {
        N = n;
        for (int v = 0; v < N; v++) { deg[v] = 0; col[v] = -1; }
        for (int i = 0; i < m && ok; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
            if (u < 0 || v < 0 || u >= N || v >= N || u == v ||
                deg[u] >= d_ || deg[v] >= d_ || has_edge(u, v)) {
                ok = 0;
                break;
            }
            add_edge(u, v);
        }
    } else {
        ok = 0;
    }
    if (!ok || !colour_graph() || cost() != 0) reset_kdd();

    save_best();
    while (now_s() < t_end) {
        if (!grow2(cap)) break;
        if (anneal(ATT, 1.0, 0.05)) save_best();
        else restore_best();
    }

    int bn = best_N;
    long cnt = 0;
    for (int u = 0; u < bn; u++)
        for (int k = 0; k < best_deg[u]; k++)
            if (best_adj[u][k] > u) cnt++;
    printf("%d %ld\n", bn, cnt);
    for (int u = 0; u < bn; u++)
        for (int k = 0; k < best_deg[u]; k++)
            if (best_adj[u][k] > u) printf("%d %d\n", u, best_adj[u][k]);
    return 0;
}
"""

GQ_Q_MAX = 9          # largest q for which W(q) is built
HAAR_FRAC = 0.1       # share of time_limit for the Haar start search
C_TIME_FRAC = 0.8     # share of time_limit for the whole run


# ---------------------------------------------------------------- algebraic bases

def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
    """W(q) for the largest prime power q <= min(d-1, GQ_Q_MAX)."""
    for q in range(min(d - 1, GQ_Q_MAX), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ---------------------------------------------------------------- Haar starts

def _search_haar(d, D, m, rng, deadline, iters):
    """Hill-climb a connection set S (|S| = d, containing 0) in Z_m so the Haar graph has diameter <= D."""
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def cost(S):
        n, edges = lib.haar_graph(m, S)
        return lib.bad_pairs(n, edges, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        cand = [x for x in others if x not in S]
        if not cand:
            break
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = rng.choice(cand)
        ct = cost(T)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


def _haar_search(d, D, rng, deadline):
    """Largest valid Haar graph found while the modulus grows."""
    best = None
    m, miss = d + 1, 0
    while time.monotonic() < deadline and miss < 5 and 2 * m <= 1200:
        S = _search_haar(d, D, m, rng, deadline, 150)
        if S is None:
            miss += 1
        else:
            best = lib.haar_graph(m, S)
            miss = 0
        m += 1
    return best


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    # Trivial cases.
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]
    kdd = lib.haar_graph(d, range(d))   # K_{d,d}: always valid for D >= 2
    if D == 2:
        return kdd

    rng = random.Random(seed)
    cands = [kdd]

    # Algebraic bases; exact Moore-type constructions are returned directly.
    base, exact = None, False
    try:
        if D == 3:
            base = _pg_base(d)
            exact = lib.is_prime_power(d - 1)
        elif D == 4:
            base = _best_gq(d)
            exact = d - 1 <= GQ_Q_MAX and lib.is_prime_power(d - 1)
    except Exception:
        base = None
    if base is not None and lib.is_valid(base[0], base[1], d, D):
        if exact:
            return base
        cands.append(base)

    # Haar starts (a different, cheap construction feeding the search).
    try:
        hg = _haar_search(d, D, rng, t0 + HAAR_FRAC * time_limit)
        if hg is not None:
            cands.append(hg)
    except Exception:
        pass

    valid = [c for c in cands if lib.is_valid(c[0], c[1], d, D)]
    if not valid:
        return kdd
    best = max(valid, key=lambda c: c[0])
    start = best

    # Bold step: local search on bipartite graphs in C. The engine repeatedly
    # adds two vertices (one per side), anneals a bad-pair cost back to zero,
    # and keeps the largest valid graph it reaches.
    elapsed = time.monotonic() - t0
    budget = C_TIME_FRAC * time_limit - elapsed - 2.0
    if budget >= 2.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                             stdin_graph=start, timeout=budget + 5.0)
            n, e = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass

    if lib.is_valid(best[0], best[1], d, D):
        return best
    return kdd
