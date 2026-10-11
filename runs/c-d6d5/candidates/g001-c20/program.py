import itertools
import time

import lib


C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define KMAX 6
#define DMAX 64
#define K2MAX 64
#define NMAX 6000

/* ---------- RNG and clock ---------- */
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double T_START = 0.0, T_BUDGET = 1.0;
static double now_sec(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}
static int time_up(void) { return now_sec() - T_START >= T_BUDGET; }

/* ---------- problem and state ----------
 * Base: k A-vertices and k B-vertices. Each layer l is a permutation sig[l] of 0..k-1,
 * so dart (l, i) goes from A_i to B_{sig[l][i]} with voltage vol[l][i] in the group.
 * Lift: A_{i,g} ~ B_{j,g*s}. Every vertex then has degree exactly d.
 * Left multiplication is an automorphism, so BFS from one representative per base
 * vertex decides diameter.
 */
static int d, D;
static int k, G, K2, M;
static int pw[K2MAX];
static int *R = NULL;          /* R[s*G+g] = g*s */
static long long capR = 0;
static int sig[DMAX][KMAX];
static int vol[DMAX][KMAX];

static int *adj = NULL, *cnt = NULL, *vis = NULL, *que = NULL;
static int capN = 0;
static int stamp = 0;

static int best_n = 0, best_m = 0;
static int *best_e = NULL;

static void ensure_buffers(int N) {
    if (N <= capN) return;
    free(adj); free(cnt); free(vis); free(que);
    adj = malloc(sizeof(int) * (size_t)N * (size_t)d);
    cnt = malloc(sizeof(int) * (size_t)N);
    vis = calloc((size_t)N, sizeof(int));
    que = malloc(sizeof(int) * (size_t)N);
    capN = N;
    stamp = 0;
}

static void ensure_R(int Gv) {
    long long need = (long long)Gv * Gv;
    if (need <= capR) return;
    free(R);
    R = malloc(sizeof(int) * (size_t)need);
    capR = need;
}

/* ---------- semidirect group Z_m x| Z_k2, element (a,b) coded a*k2+b ---------- */
static int gcd_i(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static int powmod_i(long long b, int e, int m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return (int)r;
}

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2;
    int c = y / K2, e = y % K2;
    int ra = (int)(((long long)pw[b] * c + a) % M);
    int be = (b + e) % K2;
    return ra * K2 + be;
}

static int setup_group(int k2, int Gv) {
    if (k2 < 1 || k2 > K2MAX || Gv % k2 != 0) return 0;
    int m = Gv / k2;
    if (m < 2) return 0;
    int cands[256];
    int nc = 0;
    if (k2 == 1) {
        cands[nc++] = 1;
    } else {
        for (int r = 1; r < m && nc < 256; r++)
            if (gcd_i(r, m) == 1 && powmod_i(r, k2, m) == 1 % m) cands[nc++] = r;
    }
    if (nc == 0) return 0;
    int r = cands[rndint(nc)];
    K2 = k2; M = m; G = Gv;
    ensure_R(Gv);
    pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) pw[b] = (int)((long long)pw[b - 1] * r % m);
    for (int s = 0; s < Gv; s++)
        for (int g = 0; g < Gv; g++)
            R[(long long)s * Gv + g] = gmul(g, s);
    return 1;
}

static int pick_k2(int Gv) {
    int divs[K2MAX];
    int nd = 0;
    for (int t = 1; t <= K2MAX && t <= Gv; t++)
        if (Gv % t == 0 && Gv / t >= 2) divs[nd++] = t;
    if (nd == 0) return 1;
    return divs[rndint(nd)];
}

/* ---------- cost: unreached (representative, vertex) pairs, plus duplicate-dart penalty ---------- */
static void random_state(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) sig[l][i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = sig[l][i]; sig[l][i] = sig[l][j]; sig[l][j] = t;
        }
        for (int i = 0; i < k; i++) vol[l][i] = rndint(G);
    }
}

static long long eval_cost(void) {
    int N = 2 * k * G;
    for (int v = 0; v < N; v++) cnt[v] = 0;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) {
            int j = sig[l][i], s = vol[l][i];
            const int *Rs = R + (long long)s * G;
            int baseA = i * G, baseB = (k + j) * G;
            for (int g = 0; g < G; g++) {
                int A = baseA + g, B = baseB + Rs[g];
                adj[A * d + cnt[A]++] = B;
                adj[B * d + cnt[B]++] = A;
            }
        }
    }

    /* identical darts give doubled edges */
    long long dup = 0;
    int nd = d * k;
    for (int a = 0; a < nd; a++) {
        int l1 = a / k, i1 = a % k;
        for (int b = a + 1; b < nd; b++) {
            int l2 = b / k, i2 = b % k;
            if (i1 == i2 && sig[l1][i1] == sig[l2][i2] && vol[l1][i1] == vol[l2][i2]) dup++;
        }
    }
    long long cost = dup * (long long)(4 * N);

    int reps[2 * KMAX];
    int nr = 0;
    for (int i = 0; i < k; i++) reps[nr++] = i * G;
    for (int j = 0; j < k; j++) reps[nr++] = (k + j) * G;

    for (int r = 0; r < nr; r++) {
        stamp++;
        if (stamp > 2000000000) {
            memset(vis, 0, sizeof(int) * (size_t)capN);
            stamp = 1;
        }
        int src = reps[r];
        int head = 0, tail = 0;
        vis[src] = stamp;
        que[tail++] = src;
        for (int dep = 0; dep < D && head < tail; dep++) {
            int end = tail;
            while (head < end) {
                int u = que[head++];
                const int *au = adj + (long long)u * d;
                for (int t = 0; t < d; t++) {
                    int v = au[t];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        que[tail++] = v;
                    }
                }
            }
        }
        cost += N - tail;
    }
    return cost;
}

/* ---------- simulated annealing over voltages and layer permutations ---------- */
static int run_search(long iters, double T0, double T1) {
    int N = 2 * k * G;
    ensure_buffers(N);
    random_state();
    long long cur = eval_cost();
    for (long it = 0; it < iters && cur > 0; it++) {
        if (time_up()) return 0;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int mv = rndint(2);
        if (mv == 0 || k == 1) {
            int l = rndint(d), i = rndint(k);
            int old = vol[l][i];
            int nv = rndint(G);
            if (nv == old) continue;
            vol[l][i] = nv;
            long long nc = eval_cost();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
            } else {
                vol[l][i] = old;
            }
        } else {
            int l = rndint(d), i1 = rndint(k), i2 = rndint(k);
            if (i1 == i2) continue;
            int t = sig[l][i1]; sig[l][i1] = sig[l][i2]; sig[l][i2] = t;
            long long nc = eval_cost();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
            } else {
                t = sig[l][i1]; sig[l][i1] = sig[l][i2]; sig[l][i2] = t;
            }
        }
    }
    return cur == 0;
}

static void record_solution(void) {
    int N = 2 * k * G;
    if (N <= best_n) return;
    int m = d * k * G;
    int *e = malloc(sizeof(int) * 2 * (size_t)m);
    int c = 0;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) {
            int j = sig[l][i], s = vol[l][i];
            for (int g = 0; g < G; g++) {
                e[2 * c] = i * G + g;
                e[2 * c + 1] = (k + j) * G + R[(long long)s * G + g];
                c++;
            }
        }
    free(best_e);
    best_e = e;
    best_m = m;
    best_n = N;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time [start_n]\n");
        return 1;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    T_BUDGET = atof(argv[4]);
    int start_n = (argc > 5) ? atoi(argv[5]) : 0;
    if (d < 1 || d > DMAX || D < 1 || T_BUDGET <= 0) {
        printf("0 0\n");
        return 0;
    }
    rs = (seed * 0x9E3779B97F4A7C15ULL) ^ 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 20; w++) rnd64();

    T_START = now_sec();
    best_n = start_n;

    while (!time_up()) {
        int kk = 1 + rndint(KMAX);
        int lo = best_n / 2 + 1;              /* need 2*kk*G > best_n */
        int Gmin = (lo + kk - 1) / kk;
        if (Gmin < 2) Gmin = 2;
        int span = Gmin / 10;
        if (span < 2) span = 2;
        int Gt = Gmin + rndint(span + 1);
        if (2 * kk * Gt > NMAX) continue;
        int ok = 0;
        for (int att = 0; att < 20 && !ok; att++) ok = setup_group(pick_k2(Gt), Gt);
        if (!ok) ok = setup_group(1, Gt);
        if (!ok) continue;
        k = kk;
        if (run_search(30000, 3.0, 0.05)) record_solution();
    }

    if (best_e == NULL) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", best_n, best_m);
    for (int t = 0; t < best_m; t++)
        printf("%d %d\n", best_e[2 * t], best_e[2 * t + 1]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python constructions used as safe fallbacks and as the starting bound.
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
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Entry point: fallbacks first, then the C annealer over two-layer-permutation
# voltage lifts on semidirect products with a larger base.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
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

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    elapsed = time.monotonic() - t0
    budget = min(0.8 * time_limit, time_limit - 5.0 - elapsed)
    budget = max(0.5, budget)
    timeout = max(budget + 0.5, min(budget + 3.0, time_limit - elapsed - 0.5))

    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", best_n],
                        timeout=timeout)
        n, e = lib.parse_graph_text(out)
        consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
