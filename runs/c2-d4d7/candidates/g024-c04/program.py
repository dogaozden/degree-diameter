"""Bi-Cayley search over explicit groups for the weakest target (d=4, D=7).

Change from the parent: the C engine no longer lifts a small base multigraph. It searches bi-Cayley
graphs directly. For a finite group G of order N and connection set S = {s_1..s_d}, the graph has
vertices a_g and b_g (g in G) and edges a_g ~ b_{g s}. Left multiplication is an automorphism that is
transitive on each side, so the diameter is decided exactly by two BFS runs (from a_e and from b_e).
The objective is the total excess distance from those two sources, and simulated annealing moves one
connection element at a time. Groups come from semidirect products Z_m x| Z_k and from PSL(2,p) /
PGL(2,p) times Z_k, with order N chosen just above half the current best. Each success raises the
target, and every accepted graph is re-checked with a full all-pairs test. The fallback is the best
Python construction (the H(3) hexagon incidence graph when d=4, D>=6), so every case still returns a
valid graph.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley graph search. Usage: prog d D seed time_limit < start_graph
 * Vertices a_g = g, b_g = N + g. Edge a_g ~ b_{g*s} for s in S (|S| = d).
 * Diameter is exact if BFS from a_e and from b_e has all distances <= D (left-regular action).
 * Groups: Z_m x|_r Z_k, and PSL(2,p)/PGL(2,p) x Z_k for p in {5,7,11}.
 * Output: the largest valid graph found, or the start graph if nothing larger is found.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 1200
#define MAXV 2400
#define MAXDEG 16
#define MAXBASE 672
#define HS 8192

static int d, D;
static double t_end;

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

/* ---------------------------------------------------------------- graphs */
typedef struct {
    int n;
    int deg[MAXV];
    int adj[MAXV][MAXDEG];
    unsigned char side[MAXV];
} Graph;

static Graph best;

static int add_edge(Graph *g, int u, int v) {
    if (g->deg[u] >= MAXDEG || g->deg[v] >= MAXDEG) return 0;
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
    return 1;
}

static uint64_t RA[MAXV * ((MAXV + 63) / 64)];
static uint64_t RB[MAXV * ((MAXV + 63) / 64)];

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
            memcpy(dst, src, sizeof(uint64_t) * W);
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
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXV || m < 0) return;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 0; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n) return;
        if (!add_edge(g, u, v)) return;
    }
    g->n = n;
    static int q[MAXV];
    static unsigned char seen[MAXV];
    memset(seen, 0, sizeof seen);
    for (int s = 0; s < n; s++) {
        if (seen[s]) continue;
        int h = 0, t = 0;
        seen[s] = 1;
        g->side[s] = 0;
        q[t++] = s;
        while (h < t) {
            int v = q[h++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (!seen[u]) {
                    seen[u] = 1;
                    g->side[u] = 1 - g->side[v];
                    q[t++] = u;
                } else if (g->side[u] == g->side[v]) {
                    g->n = 0;
                    return;
                }
            }
        }
    }
}

static void print_graph(const Graph *g) {
    if (g->n <= 0) { printf("0 0\n"); return; }
    long m = 0;
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) m++;
    printf("%d %ld\n", g->n, m);
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) printf("%d %d\n", u, g->adj[u][i]);
}

/* ---------------------------------------------------------------- groups */
static int GTS[MAXN * MAXN];
static int INV[MAXN];
static int NG;
static int BASE[MAXBASE * MAXBASE];
static int BASE_ORD;
static int cur_base = -1;

typedef struct { unsigned char p[16]; } Perm;
static Perm ELEM[MAXBASE];
static uint64_t hkey[HS];
static int hval[HS];

static uint64_t pkey(const unsigned char *p, int s) {
    uint64_t k = 0;
    for (int i = 0; i < s; i++) k |= (uint64_t)p[i] << (4 * i);
    return k;
}

static unsigned hslot(uint64_t k) { return (unsigned)((k * 0x9E3779B97F4A7C15ULL) >> 51); }

static int hfind(uint64_t k) {
    unsigned h = hslot(k);
    while (hval[h]) {
        if (hkey[h] == k) return hval[h] - 1;
        h = (h + 1) & (HS - 1);
    }
    return -1;
}

static void hput(uint64_t k, int idx) {
    unsigned h = hslot(k);
    while (hval[h]) h = (h + 1) & (HS - 1);
    hkey[h] = k;
    hval[h] = idx + 1;
}

/* Closure of PSL(2,p) (pgl=0) or PGL(2,p) (pgl=1) acting on P^1(F_p); identity is ELEM[0]. */
static int perm_closure(int p, int pgl, int *ordp) {
    int s = p + 1, inf = p, ng = 0, prim = 1;
    Perm gen[3];
    memset(gen, 0, sizeof gen);
    for (int c = 2; c < p; c++) {
        int ok = 1;
        for (int e = 1; e < p - 1 && ok; e++)
            if (powmod(c, e, p) == 1) ok = 0;
        if (ok) { prim = c; break; }
    }
    for (int x = 0; x <= p; x++)
        gen[ng].p[x] = (unsigned char)((x == inf) ? inf : (x + 1) % p);
    ng++;
    for (int x = 0; x <= p; x++) {
        int v;
        if (x == inf) v = 0;
        else if (x == 0) v = inf;
        else v = (int)((p - powmod(x, p - 2, p)) % p);
        gen[ng].p[x] = (unsigned char)v;
    }
    ng++;
    if (pgl) {
        for (int x = 0; x <= p; x++)
            gen[ng].p[x] = (unsigned char)((x == inf) ? inf : (x * prim) % p);
        ng++;
    }
    memset(hval, 0, sizeof hval);
    memset(&ELEM[0], 0, sizeof(Perm));
    for (int x = 0; x < s; x++) ELEM[0].p[x] = (unsigned char)x;
    hput(pkey(ELEM[0].p, s), 0);
    int n = 1;
    for (int qi = 0; qi < n; qi++) {
        for (int k = 0; k < ng; k++) {
            Perm h;
            memset(&h, 0, sizeof h);
            for (int x = 0; x < s; x++) h.p[x] = ELEM[qi].p[gen[k].p[x]];
            uint64_t key = pkey(h.p, s);
            if (hfind(key) < 0) {
                if (n >= MAXBASE) return 0;
                ELEM[n] = h;
                hput(key, n);
                n++;
            }
        }
    }
    *ordp = n;
    return 1;
}

/* Base groups: index 0..4 = PSL(2,5), PGL(2,5), PSL(2,7), PGL(2,7), PSL(2,11). */
static const int BT_P[5] = {5, 5, 7, 7, 11};
static const int BT_G[5] = {0, 1, 0, 1, 0};
static const int BT_O[5] = {60, 120, 168, 336, 660};

static int build_base(int b) {
    if (cur_base == b) return 1;
    int ord = 0;
    if (!perm_closure(BT_P[b], BT_G[b], &ord)) return 0;
    int s = BT_P[b] + 1;
    for (int i = 0; i < ord; i++)
        for (int j = 0; j < ord; j++) {
            Perm h;
            memset(&h, 0, sizeof h);
            for (int x = 0; x < s; x++) h.p[x] = ELEM[i].p[ELEM[j].p[x]];
            int idx = hfind(pkey(h.p, s));
            BASE[i * ord + j] = idx < 0 ? 0 : idx;
        }
    BASE_ORD = ord;
    cur_base = b;
    return 1;
}

static void finish_group(int N) {
    NG = N;
    for (int x = 0; x < N; x++) {
        INV[x] = 0;
        for (int y = 0; y < N; y++)
            if (GTS[x * N + y] == 0) { INV[x] = y; break; }
    }
}

static int set_perm_product(int b, int k) {
    if (!build_base(b)) return 0;
    int o = BASE_ORD;
    int N = o * k;
    if (N > MAXN || N < 1) return 0;
    for (int x = 0; x < o; x++)
        for (int c = 0; c < k; c++)
            for (int y = 0; y < o; y++)
                for (int e = 0; e < k; e++)
                    GTS[(x * k + c) * N + (y * k + e)] = BASE[x * o + y] * k + (c + e) % k;
    finish_group(N);
    return 1;
}

static int RP[MAXN];

static int set_semidirect(int m, int k, int r) {
    int N = m * k;
    if (N > MAXN || N < 1) return 0;
    RP[0] = 1 % m;
    for (int b = 1; b < k; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            GTS[x * N + y] = (int)(((a + (long)RP[b] * c) % m) * k + (b + e) % k);
        }
    }
    finish_group(N);
    return 1;
}

/* Random group of order N. */
static int random_group(int N) {
    if (rndint(2) == 0) {
        int cand[5], nc = 0;
        for (int b = 0; b < 5; b++)
            if (N % BT_O[b] == 0) cand[nc++] = b;
        if (nc > 0) {
            int b = cand[rndint(nc)];
            return set_perm_product(b, N / BT_O[b]);
        }
    }
    int divs[MAXN], nd = 0;
    for (int m = 1; m <= N; m++)
        if (N % m == 0) divs[nd++] = m;
    int m = divs[rndint(nd)], k = N / m;
    if (m == 1) return set_semidirect(1, k, 0);
    for (int t = 0; t < 60; t++) {
        int r = 1 + rndint(m - 1);
        if (gcd(r, m) == 1 && powmod(r, k, m) == 1 % m) return set_semidirect(m, k, r);
    }
    return set_semidirect(m, k, 1);
}

/* ---------------------------------------------------------------- bi-Cayley search */
static int S[MAXDEG], BESTS[MAXDEG], INVS[MAXDEG];
static int dist_[MAXV], que[MAXV];

static int in_prefix(int x, int k) {
    for (int i = 0; i < k; i++)
        if (S[i] == x) return 1;
    return 0;
}

/* Excess distance from a_e and b_e: sum of max(0, dist - D), with unreached vertices charged 2. */
static long bi_cost(void) {
    int N = NG, nv = 2 * N;
    for (int j = 0; j < d; j++) INVS[j] = INV[S[j]];
    long total = 0;
    for (int src = 0; src < 2; src++) {
        int s0 = src ? N : 0;
        for (int v = 0; v < nv; v++) dist_[v] = -1;
        int h = 0, t = 0;
        dist_[s0] = 0;
        que[t++] = s0;
        while (h < t) {
            int v = que[h++];
            int dv = dist_[v] + 1;
            if (v < N) {
                const int *row = GTS + (size_t)v * N;
                for (int j = 0; j < d; j++) {
                    int u = N + row[S[j]];
                    if (dist_[u] < 0) { dist_[u] = dv; que[t++] = u; }
                }
            } else {
                const int *row = GTS + (size_t)(v - N) * N;
                for (int j = 0; j < d; j++) {
                    int u = row[INVS[j]];
                    if (dist_[u] < 0) { dist_[u] = dv; que[t++] = u; }
                }
            }
        }
        for (int v = 0; v < nv; v++) {
            if (dist_[v] < 0) total += 2;
            else if (dist_[v] > D) total += dist_[v] - D;
        }
    }
    return total;
}

static int search_connection(double until) {
    int N = NG;
    for (int j = 0; j < d; j++) {
        int x;
        do { x = rndint(N); } while (in_prefix(x, j));
        S[j] = x;
    }
    long c = bi_cost();
    long bc = c;
    memcpy(BESTS, S, sizeof(int) * d);
    double T0 = 1.0 + 0.05 * (double)c;
    double T = T0;
    int stall = 0;
    for (long it = 0; bc > 0; it++) {
        if ((it & 63) == 0 && now() > until) break;
        int j = rndint(d);
        int old = S[j];
        int x;
        do { x = rndint(N); } while (in_prefix(x, d));
        S[j] = x;
        long nc = bi_cost();
        long delta = nc - c;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            c = nc;
        } else {
            S[j] = old;
        }
        if (c < bc) {
            bc = c;
            memcpy(BESTS, S, sizeof(int) * d);
            stall = 0;
        } else {
            stall++;
        }
        T *= 0.9993;
        if (T < 0.25) T = 0.25;
        if (stall > 3000) {
            memcpy(S, BESTS, sizeof(int) * d);
            int jj = rndint(d), y;
            do { y = rndint(N); } while (in_prefix(y, d));
            S[jj] = y;
            c = bi_cost();
            T = T0;
            stall = 0;
        }
    }
    memcpy(S, BESTS, sizeof(int) * d);
    return bc == 0;
}

static int accept_current(void) {
    static Graph tmp;
    int N = NG;
    tmp.n = 2 * N;
    for (int v = 0; v < tmp.n; v++) {
        tmp.deg[v] = 0;
        tmp.side[v] = (unsigned char)(v >= N);
    }
    for (int x = 0; x < N; x++)
        for (int j = 0; j < d; j++)
            if (!add_edge(&tmp, x, N + GTS[x * N + S[j]])) return 0;
    if (!is_valid(&tmp)) return 0;
    if (tmp.n > best.n) best = tmp;
    return 1;
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
    t_end = t0 + limit * 0.92;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    best.n = 0;
    read_start(&best);
    if (d < 2 || d > MAXDEG || D < 2) { print_graph(&best); return 0; }
    long moore = moore_bound();
    if (best.n > 0 && best.n >= moore) { print_graph(&best); return 0; }

    while (now() < t_end) {
        long lo = best.n / 2 + 1;
        if (lo < d) lo = d;
        long hi = moore / 2;
        if (hi > MAXN) hi = MAXN;
        if (lo > hi) break;
        int N = (int)(lo + rndint((int)(hi - lo + 1)));
        if (!random_group(N)) continue;
        double left = t_end - now();
        if (left <= 0) break;
        double until = now() + (left < 2.5 ? left : 2.5);
        if (search_connection(until)) accept_current();
    }
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
    """Incidence graph of the split Cayley hexagon H(3): 728 vertices, degree 4, diameter 6.

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
    """Algebraic candidates (each is built inside its own try block)."""
    out = []

    def attempt(make):
        try:
            res = make()
        except Exception:
            return
        if res is not None:
            out.append(res)

    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        attempt(lambda: lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        attempt(lambda: lib.araujo_lopez_graph(d - 2))
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            attempt(lambda: _gq_w(q))
    if d == 4 and D >= 6:
        attempt(_gh_h3)
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
    for n, e in known_starts(d, D):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 16 or D < 2 or best[0] >= lib.moore_bound(d, D):
        return best

    # The C run is timed from its own start; compilation adds about a second on top.
    budget = 0.88 * time_limit - (time.monotonic() - t0) - 3.0
    if budget < 2.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 6.0)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
