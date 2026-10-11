import itertools
import time

import lib


# C engine. Two modes:
#   haar: search a cyclic bi-Cayley (Haar) graph H(m, S) with |S| = d, which is
#         d-regular bipartite with 2m vertices. Vertex-transitivity on each side
#         means the diameter is <= D iff the balls of a0 and b0 cover the graph.
#         Simulated annealing over S finds the largest m that works.
#   lns:  kill / repair / regrow search on a general valid bipartite graph, using
#         bitset ball costs and degree-preserving double-edge switches.
C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXW 32
#define MAXD 64
#define EDGECAP (MAXN * MAXD / 2)

typedef uint64_t u64;

static int d_, D_;
static double tl_;
static clock_t t0_;
static u64 rs_ = 88172645463325252ULL;

static u64 rnd(void) { rs_ ^= rs_ << 13; rs_ ^= rs_ >> 7; rs_ ^= rs_ << 17; return rs_; }
static int rndint(int k) { return (int)(rnd() % (u64)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - t0_) / CLOCKS_PER_SEC; }

static int pc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int in_set(const int *S, int k, int x) {
    for (int i = 0; i < k; i++) if (S[i] == x) return 1;
    return 0;
}

/* ---------------- Haar (cyclic bi-Cayley) search ---------------- */

static int hdist[MAXN], hq[MAXN];
static int haar_Sout[MAXD];

/* Unreached vertices from a0 and b0 within radius D_ in H(m, S). */
static int haar_cost(int m, const int *S, int k) {
    int bad = 0;
    int N = 2 * m;
    int srcs[2] = {0, m};
    for (int si = 0; si < 2; si++) {
        for (int i = 0; i < N; i++) hdist[i] = -1;
        int h = 0, t = 0, seen = 1;
        hq[t++] = srcs[si];
        hdist[srcs[si]] = 0;
        while (h < t) {
            int u = hq[h++];
            if (hdist[u] >= D_) continue;
            for (int i = 0; i < k; i++) {
                int v;
                if (u < m) v = m + (u + S[i]) % m;
                else v = ((u - m) - S[i] + m) % m;
                if (hdist[v] < 0) {
                    hdist[v] = hdist[u] + 1;
                    hq[t++] = v;
                    seen++;
                }
            }
        }
        bad += N - seen;
    }
    return bad;
}

static int haar_try(int m, int iters, double T0) {
    int k = d_;
    int S[MAXD];
    if (m <= k) return 0;
    for (int i = 0; i < k; i++) {
        int x;
        do { x = rndint(m); } while (in_set(S, i, x));
        S[i] = x;
    }
    int cur = haar_cost(m, S, k);
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 127) == 0 && elapsed() > tl_) break;
        double T = T0 * (1.0 - (double)it / iters) + 0.02;
        int i = rndint(k);
        int x;
        do { x = rndint(m); } while (in_set(S, k, x));
        int old = S[i];
        S[i] = x;
        int nc = haar_cost(m, S, k);
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) cur = nc;
        else S[i] = old;
    }
    if (cur == 0) {
        memcpy(haar_Sout, S, sizeof(int) * (size_t)k);
        return 1;
    }
    return 0;
}

/* ---------------- LNS on general bipartite graphs ---------------- */

static int n;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static u64 bufA[MAXN][MAXW], tmpb[MAXN][MAXW], cov[MAXN][MAXW];
static int stk[MAXN];

typedef struct {
    int n;
    int deg[MAXN];
    int col[MAXN];
    int adj[MAXN][MAXD];
} St;
static St tmp_s, best_s;

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++) if (adj[a][i] == b) return 1;
    return 0;
}
static void rm_from(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (adj[a][i] == b) { adj[a][i] = adj[a][--deg[a]]; return; }
    }
}
static void add_edge(int a, int b) { adj[a][deg[a]++] = b; adj[b][deg[b]++] = a; }
static void del_edge(int a, int b) { rm_from(a, b); rm_from(b, a); }

/* out[v] = bitmask of vertices within distance r of v. */
static void balls(int r, u64 (*out)[MAXW]) {
    int W = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) out[v][w] = 0;
        out[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int k = 0; k < r; k++) {
        for (int v = 0; v < n; v++)
            for (int w = 0; w < W; w++) tmpb[v][w] = out[v][w];
        for (int v = 0; v < n; v++)
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                for (int w = 0; w < W; w++) tmpb[v][w] |= out[u][w];
            }
        for (int v = 0; v < n; v++)
            for (int w = 0; w < W; w++) out[v][w] = tmpb[v][w];
    }
}

/* Number of unordered pairs at distance > D_. Zero iff the graph is valid. */
static long cost(void) {
    int W = (n + 63) >> 6;
    balls(D_, bufA);
    long tot = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(bufA[v][w]);
        tot += n - c;
    }
    return tot / 2;
}

/* Add cross-side edges between deficient vertices (only shortens distances). */
static void fill(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] < d_) {
            if (col[v] == 0) L[nl++] = v;
            else R[nr++] = v;
        }
    }
    if (nl == 0 || nr == 0) return;
    long tries = 20L * (nl + nr) + 50;
    for (long t = 0; t < tries; t++) {
        int a = L[rndint(nl)], b = R[rndint(nr)];
        if (deg[a] < d_ && deg[b] < d_ && !has_edge(a, b)) add_edge(a, b);
    }
}

/* Append a vertex on side `side` joined to a greedy cover of the other side. */
static int add_vertex(int side) {
    if (n >= MAXN) return 0;
    int v = n++;
    col[v] = side;
    deg[v] = 0;
    balls(D_ - 1, cov);
    int W = (n + 63) >> 6;
    u64 covd[MAXW];
    for (int w = 0; w < W; w++) covd[w] = 0;
    covd[v >> 6] |= 1ULL << (v & 63);
    for (int step = 0; step < d_; step++) {
        int best = -1;
        long bs = -1;
        for (int s = 0; s < n; s++) {
            if (col[s] == side || has_edge(v, s)) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += pc64(cov[s][w] & ~covd[w]);
            if (g == 0) continue;
            long sc = (long)g * 1000 + (deg[s] < d_ ? 300 : 0) + rndint(300);
            if (sc > bs) { bs = sc; best = s; }
        }
        if (best < 0) break;
        if (deg[best] >= d_) {
            int t = adj[best][rndint(deg[best])];
            del_edge(best, t);
        }
        add_edge(v, best);
        for (int w = 0; w < W; w++) covd[w] |= cov[best][w];
    }
    fill();
    return v;
}

static void remove_vertex(int v) {
    for (int i = 0; i < deg[v]; i++) rm_from(adj[v][i], v);
    deg[v] = 0;
    int L = n - 1;
    if (v != L) {
        for (int i = 0; i < deg[L]; i++) {
            int w = adj[L][i];
            for (int j = 0; j < deg[w]; j++) {
                if (adj[w][j] == L) { adj[w][j] = v; break; }
            }
        }
        memcpy(adj[v], adj[L], sizeof(int) * MAXD);
        deg[v] = deg[L];
        col[v] = col[L];
    }
    n--;
}

/* Degree-preserving double-edge switches minimising cost. Returns final cost. */
static long anneal(int iters, double T0) {
    static int side0[MAXN];
    long cur = cost();
    int ns = 0;
    for (int v = 0; v < n; v++) if (col[v] == 0 && deg[v] > 0) side0[ns++] = v;
    if (ns < 2) return cur;
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 63) == 0 && elapsed() > tl_) break;
        int a = side0[rndint(ns)], c = side0[rndint(ns)];
        if (a == c) continue;
        int b = adj[a][rndint(deg[a])];
        int e = adj[c][rndint(deg[c])];
        if (has_edge(a, e) || has_edge(c, b)) continue;
        del_edge(a, b);
        del_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        long nc = cost();
        double T = T0 * (1.0 - (double)it / iters) + 0.02;
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
        } else {
            del_edge(a, e);
            del_edge(c, b);
            add_edge(a, b);
            add_edge(c, e);
        }
    }
    return cur;
}

static void save(St *s) {
    s->n = n;
    memcpy(s->deg, deg, sizeof(int) * (size_t)n);
    memcpy(s->col, col, sizeof(int) * (size_t)n);
    memcpy(s->adj, adj, sizeof(int) * (size_t)n * MAXD);
}

static void load(const St *s) {
    n = s->n;
    memcpy(deg, s->deg, sizeof(int) * (size_t)n);
    memcpy(col, s->col, sizeof(int) * (size_t)n);
    memcpy(adj, s->adj, sizeof(int) * (size_t)n * MAXD);
}

int main(int argc, char **argv) {
    t0_ = clock();
    if (argc < 6) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs_ ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs_ == 0) rs_ = 1;
    tl_ = atof(argv[4]);
    if (d_ < 1 || d_ > MAXD || D_ < 2) { printf("0 0\n"); return 0; }

    if (strcmp(argv[5], "haar") == 0) {
        int m = argc > 6 ? atoi(argv[6]) : d_ + 1;
        if (m < d_ + 1) m = d_ + 1;
        int bestm = 0;
        int bestS[MAXD];
        while (elapsed() < tl_ && m <= 1000) {
            int ok = 0;
            for (int r = 0; r < 20 && !ok && elapsed() < tl_; r++)
                ok = haar_try(m, 20000, 1.0);
            if (!ok) break;
            bestm = m;
            memcpy(bestS, haar_Sout, sizeof(int) * (size_t)d_);
            m++;
        }
        if (bestm == 0) { printf("0 0\n"); return 0; }
        printf("%d %d\n", 2 * bestm, bestm * d_);
        for (int i = 0; i < bestm; i++)
            for (int j = 0; j < d_; j++)
                printf("%d %d\n", i, bestm + (i + bestS[j]) % bestm);
        return 0;
    }

    /* LNS mode: read start graph from stdin. */
    static int eu[EDGECAP + 8], ev[EDGECAP + 8];
    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 < 1 || n0 > MAXN || m0 < 0 || m0 > EDGECAP) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) { printf("0 0\n"); return 0; }
    }
    n = n0;
    memset(deg, 0, sizeof deg);
    for (int i = 0; i < m0; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || has_edge(u, v) ||
            deg[u] >= d_ || deg[v] >= d_) {
            printf("0 0\n");
            return 0;
        }
        add_edge(u, v);
    }
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int top = 0;
        stk[top++] = s;
        while (top > 0) {
            int u = stk[--top];
            for (int i = 0; i < deg[u]; i++) {
                int w = adj[u][i];
                if (col[w] < 0) { col[w] = 1 - col[u]; stk[top++] = w; }
                else if (col[w] == col[u]) { printf("0 0\n"); return 0; }
            }
        }
    }
    fill();
    if (cost() != 0) { printf("0 0\n"); return 0; }

    save(&best_s);
    int best_n = n;
    int stall = 0;
    while (elapsed() < tl_) {
        save(&tmp_s);
        if (rndint(100) < 70) {
            add_vertex(rndint(2));
        } else {
            int k = 1 + rndint(2);
            for (int j = 0; j < k && n > 3; j++) remove_vertex(rndint(n));
            fill();
        }
        long c = anneal(1500, 0.6);
        if (c == 0 && n >= tmp_s.n - 1) {
            if (n > best_n) {
                save(&best_s);
                best_n = n;
                stall = 0;
            } else {
                stall++;
            }
        } else {
            load(&tmp_s);
            stall++;
        }
        if (stall > 60) {
            load(&best_s);
            stall = 0;
        }
    }
    load(&best_s);
    int m = 0;
    for (int v = 0; v < n; v++) m += deg[v];
    m /= 2;
    printf("%d %d\n", n, m);
    for (int v = 0; v < n; v++)
        for (int i = 0; i < deg[v]; i++)
            if (v < adj[v][i]) printf("%d %d\n", v, adj[v][i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured bases (Python side only).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree q + 1, diameter 4, order 2(q+1)(q^2+1).
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
    """W(q) for the largest prime power q with q + 1 <= d (q <= 16)."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def _run(args, graph, budget):
    """Run the C engine and parse its output (raises on failure)."""
    out = lib.run_c(C_SOURCE, args, stdin_graph=graph, timeout=budget + 15)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    end = t0 + 0.8 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    if not lib.is_valid(best_n, best_e, d, D):
        return 1, []

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, [tuple(x) for x in e]

    # D = 2 is optimal with K_{d,d}; tiny degree is not worth the search.
    if D == 2 or d < 3:
        return best_n, list(best_e)

    # Structured base: W(q) for D >= 4, PG(2, q) for D = 3.
    starts = []
    base = _best_gq(d) if D >= 4 else _best_pg(d)
    if base is not None and lib.is_valid(base[0], base[1], d, D):
        starts.append(base)
        consider(base[0], base[1])

    # Already at the Moore bound: nothing to gain.
    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Stage 1: cyclic bi-Cayley (Haar) search, starting near half the current order.
    m_start = max(d + 1, best_n // 2 - 2)
    hb = max(1.0, 0.35 * time_limit)
    try:
        n1, e1 = _run([d, D, seed, round(hb, 2), "haar", m_start], None, hb)
        if n1 > 0 and lib.is_valid(n1, e1, d, D):
            starts.append((n1, e1))
            consider(n1, e1)
    except (RuntimeError, ValueError):
        pass

    # Stage 2: kill / repair / regrow from each start, splitting the remaining time.
    for i, (n0, e0) in enumerate(starts):
        left = len(starts) - i
        budget = (end - time.monotonic()) / left - 0.5
        if budget < 2:
            break
        try:
            n2, e2 = _run([d, D, seed + i, round(budget, 2), "lns"], (n0, e0), budget)
            consider(n2, e2)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
