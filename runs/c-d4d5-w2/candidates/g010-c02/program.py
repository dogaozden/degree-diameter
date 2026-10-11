"""Two-stage search for d-regular bipartite graphs with diameter <= D.

Stage 1 (about 55% of the search window): voltage lifts over semidirect groups Z_m x| Z_k,
with the orbit-reduced diameter test. This stage reproduces the strongest previous method.

Stage 2 (the rest): a different construction. Unstructured d-regular bipartite graphs on n
vertices are annealed with double-edge switches, and the cost is the number of vertex pairs
at distance > D (bitset BFS). The ladder starts at the current best order + 2. Each rung starts
from the previous best grown by two vertices, with a random start as the fallback. When a rung
fails, the program returns the last valid graph.

Python builds the algebraic starts, validates them, and keeps a valid fallback in every case.
"""
import time
import itertools

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 1024
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXP 4

typedef struct { int m, k, r; int rp[MAXN]; } Grp;
typedef struct { int i, j, g; } Dart;

static int d, D, n, h;
static int adj[MAXN][MAXD];
static int badv[MAXN], curbadv[MAXN];
static int sol_adj[MAXN][MAXD];
static int sol_n;
static long cur_n;
static Dart dt[MAXD * MAXP];
static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

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

static int has(int a, int b) {
    for (int i = 0; i < d; i++)
        if (adj[a][i] == b) return 1;
    return 0;
}

static void repl(int a, int old, int nw) {
    for (int i = 0; i < d; i++)
        if (adj[a][i] == old) { adj[a][i] = nw; return; }
}

/* Double-edge switch: edges v-u and s-t (v, s on the same side) become v-t and s-u. */
static void sw(int v, int u, int s, int t) {
    repl(v, u, t);
    repl(u, v, s);
    repl(s, t, u);
    repl(t, s, v);
}

/* Number of unordered pairs at distance > D. Fills badv[v] = vertices at distance > D from v. */
static long bad_pairs(void) {
    int W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * (size_t)W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < d; i++) {
                const uint64_t *s = cur + (size_t)adj[v][i] * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
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

static void store_solution(void) {
    sol_n = n;
    cur_n = n;
    memcpy(sol_adj, adj, sizeof(adj));
}

static void print_solution(void) {
    long m = (long)sol_n * d / 2;
    printf("%d %ld\n", sol_n, m);
    for (int u = 0; u < sol_n; u++)
        for (int i = 0; i < d; i++) {
            int v = sol_adj[u][i];
            if (u < v) printf("%d %d\n", u, v);
        }
}

/* Random d-regular bipartite graph on n = 2h vertices (A = [0,h), B = [h,n)). */
static int init_random(void) {
    static int cnt[MAXN], perm[MAXN];
    for (long tries = 0; tries < 200000; tries++) {
        memset(cnt, 0, sizeof(int) * (size_t)n);
        int ok = 1;
        for (int k = 0; k < d && ok; k++) {
            for (int i = 0; i < h; i++) perm[i] = i;
            for (int i = h - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i];
                perm[i] = perm[j];
                perm[j] = s;
            }
            for (int a = 0; a < h; a++) {
                int b = h + perm[a];
                for (int i = 0; i < cnt[a]; i++)
                    if (adj[a][i] == b) { ok = 0; break; }
                if (!ok) break;
                adj[a][cnt[a]++] = b;
                adj[b][cnt[b]++] = a;
            }
        }
        if (ok) return 1;
    }
    return 0;
}

/* Grow the stored solution (order m0) by two vertices: x joins A, y joins B, x-y is an edge,
 * and d-1 disjoint edges a-b are rewired to x-b and y-a. Degrees stay d. */
static int init_grow(void) {
    static int used[MAXN];
    int m0 = sol_n, h0 = m0 / 2;
    memset(used, 0, sizeof(int) * (size_t)(m0 + 2));
    n = m0 + 2;
    h = h0 + 1;
    int x = h0, y = m0 + 1;
    for (int a = 0; a < h0; a++)
        for (int i = 0; i < d; i++) adj[a][i] = sol_adj[a][i] + 1;
    for (int b = h0; b < m0; b++)
        for (int i = 0; i < d; i++) adj[b + 1][i] = sol_adj[b][i];
    int k = 0;
    for (int tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(h0);
        int bn = adj[a][rndint(d)];
        if (used[a] || used[bn]) continue;
        used[a] = used[bn] = 1;
        repl(a, bn, y);
        repl(bn, a, x);
        adj[x][k] = bn;
        adj[y][k] = a;
        k++;
    }
    if (k < d - 1) return 0;
    adj[x][d - 1] = y;
    adj[y][d - 1] = x;
    return 1;
}

static int pick_bad_vertex(void) {
    static int list[MAXN];
    int c = 0;
    for (int v = 0; v < n; v++)
        if (curbadv[v] > 0) list[c++] = v;
    if (c == 0) return rndint(n);
    return list[rndint(c)];
}

/* Simulated annealing on double-edge switches. Returns 1 when the graph has diameter <= D. */
static int anneal(double until) {
    long cur = bad_pairs();
    memcpy(curbadv, badv, sizeof(int) * (size_t)n);
    if (cur == 0) return 1;
    double T = 3.0;
    for (long it = 1;; it++) {
        if ((it & 127) == 0 && now() > until) return 0;
        int v = rnd01() < 0.85 ? pick_bad_vertex() : rndint(n);
        int s = rndint(h) + (v >= h ? h : 0);
        if (s == v) continue;
        int u = adj[v][rndint(d)];
        int t = adj[s][rndint(d)];
        if (has(v, t) || has(s, u)) continue;
        sw(v, u, s, t);
        long nb = bad_pairs();
        long delta = nb - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nb;
            memcpy(curbadv, badv, sizeof(int) * (size_t)n);
            if (cur == 0) return 1;
        } else {
            sw(v, t, s, u);
        }
        T *= 0.99995;
        if (T < 0.3) T = 3.0;
    }
}

/* ---------------- voltage lifts over Z_m x| Z_k ---------------- */

/* Element (a, b) is coded a*k + b, with (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

static int random_group(int N, Grp *G) {
    long count = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) {
                G->m = m;
                G->k = k;
                G->r = r;
            }
        }
    }
    if (!count) return 0;
    G->rp[0] = 1 % G->m;
    for (int b = 1; b < G->k; b++)
        G->rp[b] = (int)((long)G->rp[b - 1] * G->r % G->m);
    return 1;
}

/* Random d-regular bipartite base multigraph on p + p vertices, connected. */
static void make_base(int p, int M[MAXP][MAXP]) {
    for (;;) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
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
        int seen[2 * MAXP] = {0};
        int stack[2 * MAXP];
        int top = 0, ns = 1;
        seen[0] = 1;
        stack[top++] = 0;
        while (top) {
            int v = stack[--top];
            for (int u = 0; u < 2 * p; u++) {
                if (seen[u]) continue;
                int linked = v < p ? (u >= p && M[v][u - p]) : (u < p && M[u][v - p]);
                if (linked) {
                    seen[u] = 1;
                    ns++;
                    stack[top++] = u;
                }
            }
        }
        if (ns == 2 * p) return;
    }
}

static int fresh_voltage(int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

/* Lift layout: A fibre i element x -> i*N + x; B fibre j element x -> p*N + j*N + x. */
static void build_lift(int p, int N, const Grp *G, int nd) {
    static int cnt[MAXN];
    n = 2 * p * N;
    h = p * N;
    memset(cnt, 0, sizeof(int) * (size_t)n);
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++) {
            int a = dt[t].i * N + x;
            int b = h + dt[t].j * N + gmul(G, x, dt[t].g);
            adj[a][cnt[a]++] = b;
            adj[b][cnt[b]++] = a;
        }
}

/* Orbit-reduced objective: BFS from the 2p fibre representatives only. */
static long orbit_bad(int p, int N) {
    static int dist[MAXN], q[MAXN];
    long total = 0;
    for (int b = 0; b < 2 * p; b++) {
        int src = b * N;
        for (int v = 0; v < n; v++) dist[v] = -1;
        int head = 0, tail = 0;
        dist[src] = 0;
        q[tail++] = src;
        while (head < tail) {
            int v = q[head++];
            if (dist[v] >= D) continue;
            for (int i = 0; i < d; i++) {
                int u = adj[v][i];
                if (dist[u] < 0) {
                    dist[u] = dist[v] + 1;
                    q[tail++] = u;
                }
            }
        }
        total += n - tail;
    }
    return total;
}

static int lift_try(int p, int N, const Grp *G, int steps, double until) {
    int M[MAXP][MAXP];
    int nd = 0;
    make_base(p, M);
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i;
                dt[nd].j = j;
                dt[nd].g = c == 0 ? 0 : fresh_voltage(nd, -1, i, j, N);
                nd++;
            }
    build_lift(p, N, G, nd);
    long bad = orbit_bad(p, N);
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 31) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(nd, t, dt[t].i, dt[t].j, N);
        build_lift(p, N, G, nd);
        long nb = orbit_bad(p, N);
        if (nb <= bad || rnd01() < 0.02) bad = nb;
        else dt[t].g = old;
    }
    build_lift(p, N, G, nd);
    return bad == 0;
}

static void lift_search(double until) {
    static Grp G;
    long moore = moore_bound();
    while (now() < until) {
        int r = rndint(20);
        int p = r < 8 ? 1 : r < 14 ? 2 : r < 18 ? 3 : 4;
        long target = cur_n + 2;
        if (target > moore) return;
        long Nmin = (target + 2L * p - 1) / (2L * p);
        int N = (int)Nmin + rndint(3);
        if (N < d) N = d;
        if (2L * p * N > moore || 2 * p * N > MAXN) continue;
        if (!random_group(N, &G)) continue;
        for (int a = 0; a < 3 && now() < until; a++) {
            if (lift_try(p, N, &G, 20000, until) && bad_pairs() == 0) {
                store_solution();
                break;
            }
        }
    }
}

/* Ladder: grow the best valid graph by two vertices and anneal. Each rung uses a grown start
 * first (half the remaining time) and then a random start. Stops at the first failed rung. */
static void ladder(double t_total) {
    long moore = moore_bound();
    for (;;) {
        if (now() >= t_total) break;
        long target = cur_n + 2;
        if (target < 2L * d) target = 2L * d;
        if (target & 1) target++;
        if (target > moore || target > MAXN) break;
        n = (int)target;
        h = n / 2;
        int ok = 0;
        if (sol_n > 0 && sol_n == cur_n && init_grow())
            ok = anneal(now() + 0.5 * (t_total - now()));
        if (!ok) {
            n = (int)target;
            h = n / 2;
            if (!init_random()) break;
            ok = anneal(t_total);
        }
        if (!ok) break;
        store_solution();
    }
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit hint_n\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long hint = atol(argv[5]);
    double t0 = now();
    double span = limit * 0.9;
    double t_total = t0 + span;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    sol_n = 0;
    cur_n = (hint >= 0 && hint <= MAXN) ? hint : 0;
    if (cur_n & 1) cur_n = 0;
    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    lift_search(t0 + span * 0.55);
    ladder(t_total);
    if (sol_n > 0 && sol_n > hint) print_solution();
    else printf("0 0\n");
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

    if d > 31 or D < 2 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.88 * time_limit - (time.monotonic() - t0) - 1.5
    if budget <= 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best[0]],
                         stdin_graph=None, timeout=budget + 5)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
