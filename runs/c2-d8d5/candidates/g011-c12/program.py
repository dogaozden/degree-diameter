"""Bi-Cayley search over semidirect products, grown in C by an exponential ladder on the group order."""
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
# C engine: Cayley-type bipartite search over semidirect groups Z_m x|_r Z_k.
#
# Vertices A_g = g and B_h = N + h. Connection set S = {s_1..s_d} in the group G
# gives edges A_g ~ B_{g*s_i}. Left multiplication is an automorphism, so the
# graph is transitive on each side. The diameter condition therefore reduces to
# two BFS runs (from A_e and from B_e). Simulated annealing on S minimises the
# number of unreached vertices. An exponential ladder over |G| keeps the largest
# order found.
# ----------------------------------------------------------------------------

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
#define CAP 40000

static int d, D;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

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
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 1000000L) break;
    }
    return 2 * s;
}

/* ---------- group Z_M x|_R Z_K, element a*K+b ---------- */
static int GM, GK, GR, GN;
static int rp[MAXN];
static int cm[CAP], ck[CAP], cr[CAP];

static void set_group(int M, int K, int R) {
    GM = M; GK = K; GR = R; GN = M * K;
    rp[0] = 1 % M;
    for (int b = 1; b < K; b++) rp[b] = (int)((long)rp[b - 1] * R % M);
}

static int gmul(int x, int y) {
    int K = GK, M = GM;
    int a = x / K, b = x % K, c = y / K, e = y % K;
    return (int)(((long)a + (long)rp[b] * c) % M) * K + (b + e) % K;
}

static int ginv(int x) {
    int K = GK, M = GM;
    int a = x / K, b = x % K;
    int nb = (K - b) % K;
    int na = (int)(((long)rp[nb] * a) % M);
    na = (M - na) % M;
    return na * K + nb;
}

static int pick_group(int N) {
    int nc = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            if (nc < CAP) { cm[nc] = 1; ck[nc] = k; cr[nc] = 0; nc++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (nc < CAP) { cm[nc] = m; ck[nc] = k; cr[nc] = r; nc++; }
        }
    }
    if (!nc) return 0;
    int c = rndint(nc);
    set_group(cm[c], ck[c], cr[c]);
    return 1;
}

/* ---------- connection set and multiplication tables ---------- */
static int S[MAXD];
static int Rs[MAXD][MAXN];   /* Rs[i][g] = g * s_i   (A -> B) */
static int Ri[MAXD][MAXN];   /* Ri[i][h] = h * s_i^-1 (B -> A) */

static void set_gen(int i, int s) {
    S[i] = s;
    int si = ginv(s);
    for (int g = 0; g < GN; g++) {
        Rs[i][g] = gmul(g, s);
        Ri[i][g] = gmul(g, si);
    }
}

static int in_prefix(int s, int k) {
    for (int i = 0; i < k; i++) if (S[i] == s) return 1;
    return 0;
}

static int in_S(int s) {
    for (int i = 0; i < d; i++) if (S[i] == s) return 1;
    return 0;
}

/* ---------- BFS on the bipartite lift ---------- */
static int vis[2 * MAXN];
static int vstamp = 0;
static int qb[2 * MAXN];
static int cntA, cntB;

static int bfs(int src) {
    int N = GN;
    vstamp++;
    int head = 0, tail = 0;
    vis[src] = vstamp;
    qb[tail++] = src;
    for (int lev = 0; lev < D; lev++) {
        int end = tail;
        if (head == end) break;
        for (; head < end; head++) {
            int v = qb[head];
            if (v < N) {
                for (int i = 0; i < d; i++) {
                    int w = N + Rs[i][v];
                    if (vis[w] != vstamp) { vis[w] = vstamp; qb[tail++] = w; }
                }
            } else {
                int h = v - N;
                for (int i = 0; i < d; i++) {
                    int w = Ri[i][h];
                    if (vis[w] != vstamp) { vis[w] = vstamp; qb[tail++] = w; }
                }
            }
        }
    }
    cntA = 0;
    for (int t = 0; t < tail; t++) if (qb[t] < N) cntA++;
    cntB = tail - cntA;
    return tail;
}

/* Number of unreached vertices, using transitivity: 0 iff the graph has diameter <= D. */
static int cost_eval(void) {
    int N = GN;
    int t1 = bfs(0);
    int c = 2 * N - t1;
    bfs(N);
    c += N - cntB;
    return c;
}

/* ---------- best solution so far ---------- */
static int best_ok = 0;
static int bestM, bestK, bestR, bestN;
static int bestS[MAXD];

static void store_best(int N) {
    bestM = GM; bestK = GK; bestR = GR; bestN = N;
    for (int i = 0; i < d; i++) bestS[i] = S[i];
    best_ok = 1;
}

/* Try to find S with diameter <= D in a random group of order N. */
static int attempt(int N, double until) {
    if (!pick_group(N)) return 0;
    if (N == d) {
        for (int i = 0; i < d; i++) set_gen(i, i);
        if (cost_eval() == 0) { store_best(N); return 1; }
        return 0;
    }
    for (int i = 0; i < d; i++) {
        int s;
        do { s = rndint(N); } while (in_prefix(s, i));
        set_gen(i, s);
    }
    int cost = cost_eval();
    double start = now();
    double dur = until - start;
    if (dur <= 0) dur = 1e-3;
    double T = 1.0;
    long it = 0;
    while (cost > 0) {
        if ((it & 63) == 0) {
            double t = now();
            if (t > until) break;
            double prog = (t - start) / dur;
            if (prog < 0) prog = 0;
            if (prog > 1) prog = 1;
            T = 0.05 + 1.5 * (1.0 - prog);
        }
        it++;
        int i = rndint(d);
        int old = S[i];
        int s;
        do { s = rndint(N); } while (in_S(s));
        set_gen(i, s);
        int c2 = cost_eval();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
        } else {
            set_gen(i, old);
        }
    }
    if (cost == 0) { store_best(N); return 1; }
    return 0;
}

static void print_best(void) {
    if (!best_ok) {
        printf("%d %d\n", 2 * d, d * d);
        for (int a = 0; a < d; a++)
            for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
        return;
    }
    set_group(bestM, bestK, bestR);
    int N = bestN;
    printf("%d %d\n", 2 * N, N * d);
    for (int g = 0; g < N; g++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", g, N + gmul(g, bestS[i]));
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    double total = limit * 0.9 - 0.5;
    if (total < 0.5) total = 0.5;
    t_end = t0 + total;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || D < 2 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }
    long moore = moore_bound();
    long cap = moore / 2;
    if (cap > MAXN) cap = MAXN;
    if (cap < d) cap = d;

    long lo = d - 1, j = 1;
    double slice_base = total * 0.12;
    if (slice_base < 1.0) slice_base = 1.0;
    while (now() < t_end) {
        if (lo + j > cap) {
            j = cap - lo;
            if (j < 1) break;
        }
        long cur = lo + j;
        double rem = t_end - now();
        if (rem <= 0) break;
        double slice = rem < slice_base ? rem : slice_base;
        if (attempt((int)cur, now() + slice)) {
            lo = cur;
            j *= 2;
        } else if (j > 1) {
            j /= 2;
        }
    }
    print_best();
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

    # Safe fallback: K_{d,d} has diameter 2 (valid for D >= 2).
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Replace the current best if (n, e) is a larger valid graph."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions.
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

    # Main search: Cayley-type bipartite graphs over semidirect products, in C.
    if D >= 2 and 2 <= d <= 32:
        c_budget = end - time.monotonic() - 0.5
        if c_budget > 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                                 stdin_graph=None, timeout=c_budget + 8)
                n, e = lib.parse_graph_text(text)
                consider(n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
