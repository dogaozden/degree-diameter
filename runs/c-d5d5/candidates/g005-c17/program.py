"""Bold variant: bi-Cayley lifts over semidirect products Z_m x| Z_k with k in {1,2,3,4}
per-side vertices, searched by simulated annealing on connection elements and layer
permutations. Cost = unreached (representative, vertex) pairs + duplicate-dart penalty.
Every accepted lift is re-verified in full by C before it is kept. Falls back to K_{d,d}
or to the known constructions in Python when nothing better is found."""
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

#define MAXN 2048
#define MAXD 16
#define MAXK 4
#define MAXG 1024
#define MAXT (MAXD * MAXK)
#define W_DUP 20

static int d, D;
static double t_end;
static long moore;

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

static int gcd_i(int a, int b) {
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

static long compute_moore(void) {
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

/* ---------------------------------------------------------------- groups */

/* Z_m x|_r Z_k2, element (a,b) = a*k2+b, (a,b)(c,e) = (a + r^b c, b+e). */
static int GM, GK, GR, NG;
static int RP[MAXG];
static int MT[MAXG * MAXG];

static void set_group(int m, int k2, int r) {
    GM = m; GK = k2; GR = r; NG = m * k2;
    for (int b = 0; b < k2; b++) RP[b] = (int)powmod(r, b, m);
    for (int x = 0; x < NG; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < NG; y++) {
            int c = y / k2, e = y % k2;
            MT[x * NG + y] = (int)((((long)a + (long)RP[b] * c) % m) * k2 + (b + e) % k2);
        }
    }
}

/* Uniform random choice among all valid (m, k2, r) with m*k2 = N. */
static void set_random_group(int N) {
    int cnt = 0, bm = 1, bk = N, br = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k2 = N / m;
        for (int r = 0; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod(r, k2, m) != 1 % m) continue;
            cnt++;
            if (rndint(cnt) == 0) { bm = m; bk = k2; br = r; }
        }
    }
    set_group(bm, bk, br);
}

/* ---------------------------------------------------------------- lifts */

static int K, TD;                 /* K vertices per side, TD = d*K darts */
static int dJ[MAXT], dS[MAXT];    /* dart t = l*K+i joins A_i to B_{dJ[t]} with voltage dS[t] */
static int adjL[MAXN][MAXD];
static int degL[MAXN];
static unsigned visL[MAXN];
static int qL[MAXN];
static unsigned stampL = 0;

static int build_adj(void) {
    int k = K, N = NG, n = 2 * k * N;
    for (int v = 0; v < n; v++) degL[v] = 0;
    for (int t = 0; t < TD; t++) {
        int I = t % k, J = dJ[t], s = dS[t];
        for (int g = 0; g < N; g++) {
            int a = I * N + g;
            int b = (k + J) * N + MT[g * N + s];
            adjL[a][degL[a]++] = b;
            adjL[b][degL[b]++] = a;
        }
    }
    return n;
}

/* Number of vertices within distance D of src (including src). */
static int reach_count(int src) {
    unsigned st = ++stampL;
    int head = 0, tail = 0;
    visL[src] = st;
    qL[tail++] = src;
    for (int lev = 0; lev < D && head < tail; lev++) {
        int end = tail;
        while (head < end) {
            int u = qL[head++];
            for (int i = 0; i < degL[u]; i++) {
                int v = adjL[u][i];
                if (visL[v] != st) { visL[v] = st; qL[tail++] = v; }
            }
        }
    }
    return tail;
}

/* Left multiplication is an automorphism, so BFS from A_i,e and B_j,e suffices. */
static long lift_cost(void) {
    int k = K;
    int n = build_adj();
    long pen = 0;
    for (int t = 0; t < TD; t++)
        for (int u = 0; u < t; u++)
            if (t % k == u % k && dJ[t] == dJ[u] && dS[t] == dS[u]) pen++;
    long unreached = 0;
    for (int i = 0; i < k; i++) unreached += n - reach_count(i * NG);
    for (int j = 0; j < k; j++) unreached += n - reach_count((k + j) * NG);
    return pen * W_DUP + unreached;
}

static void random_darts(void) {
    int perm[MAXK];
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1), s = perm[i];
            perm[i] = perm[j];
            perm[j] = s;
        }
        for (int i = 0; i < K; i++) {
            dJ[l * K + i] = perm[i];
            dS[l * K + i] = rndint(NG);
        }
    }
}

/* Simulated annealing on the current random lift. Returns final cost (0 = success). */
static long anneal(long steps, double until) {
    long c = lift_cost();
    const double T0 = 1.5, T1 = 0.05;
    double T = T0;
    for (long s = 0; s < steps && c > 0; s++) {
        if ((s & 1023) == 0) {
            if (now() > until) break;
            T = T0 * pow(T1 / T0, (double)s / (double)steps);
        }
        if (K > 1 && rnd01() < 0.25) {
            int l = rndint(d), a = rndint(K), b = rndint(K);
            if (a == b) continue;
            int t1 = l * K + a, t2 = l * K + b;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            long c2 = lift_cost();
            if (c2 <= c || rnd01() < exp((double)(c - c2) / T)) c = c2;
            else { tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp; }
        } else {
            int t = rndint(TD);
            int old = dS[t];
            int nv = rndint(NG);
            if (nv == old) continue;
            dS[t] = nv;
            long c2 = lift_cost();
            if (c2 <= c || rnd01() < exp((double)(c - c2) / T)) c = c2;
            else dS[t] = old;
        }
    }
    return c;
}

/* Full independent check of the current lift as a simple graph with max degree d and diameter D. */
static int full_check(void) {
    int n = build_adj();
    for (int v = 0; v < n; v++) {
        if (degL[v] > d) return 0;
        for (int i = 0; i < degL[v]; i++) {
            if (adjL[v][i] == v) return 0;
            for (int j = 0; j < i; j++)
                if (adjL[v][j] == adjL[v][i]) return 0;
        }
    }
    for (int v = 0; v < n; v++)
        if (reach_count(v) != n) return 0;
    return 1;
}

/* ---------------------------------------------------------------- best store */

static int have = 0;
static int bK, bN, bGM, bGK, bGR;
static int bDJ[MAXT], bDS[MAXT];

static void save_best(void) {
    have = 1;
    bK = K; bN = NG; bGM = GM; bGK = GK; bGR = GR;
    memcpy(bDJ, dJ, sizeof(int) * TD);
    memcpy(bDS, dS, sizeof(int) * TD);
}

static void print_result(void) {
    if (!have) {
        if (d < 1 || D < 2) { printf("0 0\n"); return; }
        printf("%d %d\n", 2 * d, d * d);
        for (int a = 0; a < d; a++)
            for (int b = 0; b < d; b++)
                printf("%d %d\n", a, d + b);
        return;
    }
    K = bK;
    set_group(bGM, bGK, bGR);
    TD = d * K;
    for (int t = 0; t < TD; t++) { dJ[t] = bDJ[t]; dS[t] = bDS[t]; }
    int k = K, N = NG;
    int n = 2 * k * N;
    long m = (long)TD * N;
    printf("%d %ld\n", n, m);
    for (int t = 0; t < TD; t++) {
        int I = t % k, J = dJ[t], s = dS[t];
        for (int g = 0; g < N; g++)
            printf("%d %d\n", I * N + g, (k + J) * N + MT[g * N + s]);
    }
}

/* ---------------------------------------------------------------- main */

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
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();
    { int a, b; (void)!scanf("%d %d", &a, &b); }

    moore = compute_moore();
    if (d < 1 || d > MAXD || D < 2) {
        print_result();
        return 0;
    }

    static const int KC[8] = {1, 1, 1, 1, 2, 2, 3, 4};
    int fails = 0;
    while (now() < t_end) {
        int cur = have ? 2 * bK * bN : 2 * d;
        if ((long)cur + 2 > moore) break;
        int k = KC[rndint(8)];
        long Nmin = ((long)cur + 2 + 2L * k - 1) / (2L * k);
        long Nl = Nmin + rndint(2);
        if (2L * k * Nl > moore || 2L * k * Nl > MAXN || Nl > MAXG) {
            if (++fails > 100000) break;
            continue;
        }
        int N = (int)Nl;
        K = k;
        TD = d * K;
        set_random_group(N);
        random_darts();
        long c = anneal(200000, t_end);
        if (c == 0 && full_check())
            save_best();
    }
    print_result();
    return 0;
}
'''


def _known_start(d, D):
    """Best directly constructible graph for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record family 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return (1, [])
    if D == 1:
        return (2, [(0, 1)])

    best = lib.haar_graph(d, range(d))   # K_{d,d}: valid for D >= 2

    def consider(cand):
        nonlocal best
        if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand

    start = _known_start(d, D)
    if start is not None:
        consider(start)

    if best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.75 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 2.0:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=None, timeout=budget + 8)
        consider(lib.parse_graph_text(text))
    except (RuntimeError, ValueError):
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
