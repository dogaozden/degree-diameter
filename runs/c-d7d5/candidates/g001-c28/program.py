import itertools
import time

import lib


# C engine: bi-Cayley lift search over Z_M x| Z_K2 with a growing-order ladder.
C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 32
#define MAXK 8
#define ITERS 8000
#define PEN 1000

/* State of a base with K vertices per side: d layers, each a permutation P[l]
   with voltage SV[l][i] on dart (i -> P[l][i]). Dart (i,j,s) joins A_{i,g} to B_{j,g*s}. */
typedef struct {
    int P[MAXD][MAXK];
    int PI[MAXD][MAXK];
    int SV[MAXD][MAXK];
    int SVI[MAXD][MAXK];
} State;

static int dD, DIAM, K, G, M, K2, R;
static long long powR[64];
static State st;
static int *stamp_arr = NULL, *queue_arr = NULL;
static int alloc_N = 0;
static int gen_ctr = 0;
static uint64_t rs = 1;
static int best_n = 0, best_m = 0;
static int *best_e = NULL;

static double now_sec(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static uint64_t rnext(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rnd(int n) { return (int)(rnext() % (uint64_t)n); }
static double rndu(void) { return (double)(rnext() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Group element x = a*K2 + b, (a,b)*(c,d) = (a + R^b c, b + d). */
static int mulg(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    long long t = ((long long)a + powR[b] * (long long)c) % M;
    int bb = (b + e) % K2;
    return (int)(t * K2 + bb);
}

/* Inverse: (a,b)^-1 = (-R^(-b) a, -b). */
static int invg(int x) {
    int a = x / K2, b = x % K2;
    int nb = (K2 - b) % K2;
    long long t = (powR[nb] * (long long)a) % M;
    long long aa = (M - t) % M;
    return (int)(aa * K2 + nb);
}

/* Choose a group of order Gt: Z_M x| Z_K2 with K2 | Gt, or cyclic if no action is found. */
static void setup_group(int Gt) {
    static const int cand[] = {2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};
    int opts[32], no = 0;
    opts[no++] = 1;
    for (int q = 0; q < (int)(sizeof cand / sizeof cand[0]); q++)
        if (Gt % cand[q] == 0 && Gt / cand[q] >= 3) opts[no++] = cand[q];
    int k2 = opts[rnd(no)];
    G = Gt;
    if (k2 > 1) {
        int m = Gt / k2;
        int found = 0, r = 1;
        for (int t = 0; t < 200 && !found; t++) {
            int c = 2 + rnd(m - 2);
            if (gcd_i(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = c; found = 1; }
        }
        if (found) {
            K2 = k2; M = m; R = r;
            powR[0] = 1 % m;
            for (int b = 1; b < K2; b++) powR[b] = powR[b - 1] * R % m;
            return;
        }
    }
    K2 = 1; M = Gt; R = 1;
    powR[0] = 1;
}

static void random_state(void) {
    for (int l = 0; l < dD; l++) {
        int perm[MAXK];
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rnd(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < K; i++) {
            st.P[l][i] = perm[i];
            st.PI[l][perm[i]] = i;
            int s = rnd(G);
            st.SV[l][i] = s;
            st.SVI[l][i] = invg(s);
        }
    }
}

/* Unreached (representative, vertex) pairs within DIAM, plus duplicate-dart penalty.
   Left multiplication is an automorphism, so BFS from A_{i,0} and B_{j,0} suffices. */
static int cost_eval(void) {
    int N = 2 * K * G, KG = K * G;
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < dD; l1++)
            for (int l2 = l1 + 1; l2 < dD; l2++)
                if (st.P[l1][i] == st.P[l2][i] && st.SV[l1][i] == st.SV[l2][i]) dup++;
    if (gen_ctr > 2000000000) {
        memset(stamp_arr, 0, sizeof(int) * (size_t)alloc_N);
        gen_ctr = 0;
    }
    long total = 0;
    for (int rep = 0; rep < 2 * K; rep++) {
        int src = rep < K ? rep * G : KG + (rep - K) * G;
        int head = 0, tail = 0;
        gen_ctr++;
        stamp_arr[src] = gen_ctr;
        queue_arr[tail++] = src;
        for (int depth = 0; depth < DIAM && head < tail; depth++) {
            int end = tail;
            while (head < end) {
                int u = queue_arr[head++];
                if (u < KG) {
                    int i = u / G, g = u % G;
                    for (int l = 0; l < dD; l++) {
                        int v = KG + st.P[l][i] * G + mulg(g, st.SV[l][i]);
                        if (stamp_arr[v] != gen_ctr) { stamp_arr[v] = gen_ctr; queue_arr[tail++] = v; }
                    }
                } else {
                    int w = u - KG, j = w / G, h = w % G;
                    for (int l = 0; l < dD; l++) {
                        int i = st.PI[l][j];
                        int v = i * G + mulg(h, st.SVI[l][i]);
                        if (stamp_arr[v] != gen_ctr) { stamp_arr[v] = gen_ctr; queue_arr[tail++] = v; }
                    }
                }
            }
        }
        total += N - tail;
    }
    return (int)(total + (long)PEN * dup);
}

/* Simulated annealing. Returns 1 on success, 0 on failure, -1 on timeout. */
static int anneal(int iters, double T0, double T1, double deadline) {
    random_state();
    int cost = cost_eval();
    State saved;
    for (int it = 0; it < iters && cost > 0; it++) {
        if ((it & 31) == 0 && now_sec() > deadline) return -1;
        saved = st;
        if (K > 1 && rnd(3) == 0) {
            int l = rnd(dD), i1 = rnd(K), i2 = rnd(K - 1);
            if (i2 >= i1) i2++;
            int a = st.P[l][i1], b = st.P[l][i2];
            st.P[l][i1] = b; st.P[l][i2] = a;
            st.PI[l][b] = i1; st.PI[l][a] = i2;
        } else {
            int l = rnd(dD), i = rnd(K), s = rnd(G);
            st.SV[l][i] = s;
            st.SVI[l][i] = invg(s);
        }
        int c2 = cost_eval();
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / T)) cost = c2;
        else st = saved;
    }
    return cost == 0;
}

static void store_best(void) {
    int KG = K * G, m = dD * KG;
    int *buf = malloc(sizeof(int) * 2 * (size_t)m);
    int idx = 0;
    for (int l = 0; l < dD; l++)
        for (int i = 0; i < K; i++) {
            int j = st.P[l][i], s = st.SV[l][i];
            for (int g = 0; g < G; g++) {
                buf[2 * idx] = i * G + g;
                buf[2 * idx + 1] = KG + j * G + mulg(g, s);
                idx++;
            }
        }
    free(best_e);
    best_e = buf;
    best_m = m;
    best_n = 2 * KG;
}

static void set_complete(int d) {
    best_n = 2 * d;
    best_m = d * d;
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)best_m);
    int idx = 0;
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++) {
            best_e[2 * idx] = i;
            best_e[2 * idx + 1] = d + j;
            idx++;
        }
}

static void print_best(void) {
    printf("%d %d\n", best_n, best_m);
    for (int e = 0; e < best_m; e++)
        printf("%d %d\n", best_e[2 * e], best_e[2 * e + 1]);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time\n");
        return 1;
    }
    int d = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs = strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    double t_end = now_sec() + tl;
    if (d < 1) {
        printf("1 0\n");
        return 0;
    }
    dD = d;
    set_complete(d);
    if (d > MAXD || DIAM < 2) {
        print_best();
        return 0;
    }

    /* Ladder: each success gives a strictly larger order than the best so far. */
    while (now_sec() < t_end) {
        int k = 1 + rnd(4);
        int base = best_n / (2 * k);
        int Gt = base + 1 + rnd(3);
        if (Gt < 3) Gt = 3;
        setup_group(Gt);
        K = k;
        int N = 2 * K * G;
        if (N > alloc_N) {
            free(stamp_arr);
            free(queue_arr);
            stamp_arr = calloc((size_t)N, sizeof(int));
            queue_arr = malloc(sizeof(int) * (size_t)N);
            alloc_N = N;
        }
        int ok = anneal(ITERS, 3.0, 0.1, t_end);
        if (ok < 0) break;
        if (ok && 2 * K * G > best_n) store_best();
    }
    print_best();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions (unchanged from the parent).
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
# Build: exact constructions first, then the C lift search with the remaining time.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Search: the C engine climbs from the best order it can certify.
    elapsed = time.monotonic() - t0
    budget = max(1.0, min(0.8 * time_limit, time_limit - 6.0 - elapsed))
    timeout = max(budget + 2.0, time_limit - elapsed - 2.0)
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)], timeout=timeout)
        n, e = lib.parse_graph_text(out)
        consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
