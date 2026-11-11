"""Bold variant: annealed voltage lifts over metacyclic groups, aimed at orders above the record.

Strategy:
  * Build a lift of a random d-regular base with P vertices per side (P = 1..4) over a random
    metacyclic group Z_m x|_r Z_k of order N, so the order is 2*P*N.
  * Left translation is an automorphism of the lift, so pairs are covered by BFS from the 2P
    representatives (A_i, e) and (B_j, e). The annealing cost is the number of unreached pairs.
  * Simulated annealing on the dart voltages (not greedy hill-climbing), with fresh base and
    group for every attempt, and a target order that climbs above the best found so far.
  * Every saved graph passes an explicit full check. Python re-checks with lib.is_valid and
    keeps a valid fallback (the Moore graph / Araujo-Lopez / K_{d,d} starts).
"""
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

#define MAXV 2048
#define MAXG 1024
#define MAXD 16
#define MAXP 4
#define MAXDART (MAXD * MAXP)

typedef struct { int i, j, g, gi; } Dart; /* A_i -- B_j with voltage g; gi = g^{-1} */

static int d, D;
static double t_end;

/* current group Z_GM x|_GR Z_GK, element a*GK+b */
static int GM, GK, GR;
static int RP[MAXG];

/* current lift: P base vertices per side, fibre size N, ND darts */
static int P, N, ND;
static Dart DT[MAXDART];

/* best saved lift */
static int bestn = 0;
static int bP, bN, bND, bGM, bGK, bGR;
static Dart bDT[MAXDART];

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

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return D >= 1 ? 2 : 1;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

/* ------------------------------------------------------------ group arithmetic */

static void set_group(int m, int k, int r) {
    GM = m; GK = k; GR = r;
    RP[0] = 1 % m;
    for (int b = 1; b < k; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
}

static inline int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    return (int)(((long)a + (long)RP[b] * c) % GM) * GK + (b + e) % GK;
}

static inline int ginv(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    int c = (int)((GM - ((long)RP[nb] * a) % GM) % GM);
    return c * GK + nb;
}

/* Uniform random (m, k, r) with m*k = n, gcd(r,m)=1, r^k = 1 mod m. */
static int pick_group(int n) {
    long cnt = 0;
    int bm = 1, bk = n, br = 0;
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        if (m == 1) {
            cnt++;
            if (rndint((int)cnt) == 0) { bm = 1; bk = k; br = 0; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            cnt++;
            if (rndint((int)cnt) == 0) { bm = m; bk = k; br = r; }
        }
    }
    set_group(bm, bk, br);
    return 1;
}

/* ------------------------------------------------------------ base and lift */

/* Random d-regular base on P+P vertices (sum of d permutation matrices), connected. */
static void make_base(int M[MAXP][MAXP]) {
    for (;;) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < P; i++) perm[i] = i;
            for (int i = P - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
            }
            for (int i = 0; i < P; i++) M[i][perm[i]]++;
        }
        int seen[2 * MAXP];
        int st[2 * MAXP];
        int top = 0, ns = 1;
        memset(seen, 0, sizeof(seen));
        seen[0] = 1;
        st[top++] = 0;
        while (top) {
            int v = st[--top];
            for (int u = 0; u < 2 * P; u++) {
                if (seen[u]) continue;
                int linked;
                if (v < P) linked = (u >= P) && M[v][u - P] > 0;
                else linked = (u < P) && M[u][v - P] > 0;
                if (linked) { seen[u] = 1; ns++; st[top++] = u; }
            }
        }
        if (ns == 2 * P) return;
    }
}

static int clash(int t, int g) {
    for (int s = 0; s < ND; s++)
        if (s != t && DT[s].g == g && DT[s].i == DT[t].i && DT[s].j == DT[t].j) return 1;
    return 0;
}

static void set_volt(int t, int g) {
    DT[t].g = g;
    DT[t].gi = ginv(g);
}

/* New random base and random voltages (distinct within each base pair). Needs P, N, group set. */
static void init_attempt(void) {
    int M[MAXP][MAXP];
    make_base(M);
    ND = 0;
    for (int i = 0; i < P; i++)
        for (int j = 0; j < P; j++)
            for (int c = 0; c < M[i][j]; c++) {
                DT[ND].i = i;
                DT[ND].j = j;
                DT[ND].g = -1;
                DT[ND].gi = -1;
                ND++;
            }
    for (int t = 0; t < ND; t++) {
        int g;
        do { g = rndint(N); } while (clash(t, g));
        set_volt(t, g);
    }
}

/* Number of vertices within distance D of src (src included). */
static int reach_from(int src) {
    static int dist[MAXV], q[MAXV];
    int V = 2 * P * N, PN = P * N;
    for (int v = 0; v < V; v++) dist[v] = -1;
    int head = 0, tail = 0, cnt = 1;
    dist[src] = 0;
    q[tail++] = src;
    while (head < tail) {
        int v = q[head++];
        if (dist[v] >= D) continue;
        int nd_ = dist[v] + 1;
        if (v < PN) {
            int i = v / N, x = v % N;
            for (int t = 0; t < ND; t++) {
                if (DT[t].i != i) continue;
                int w = PN + DT[t].j * N + gmul(x, DT[t].g);
                if (dist[w] < 0) { dist[w] = nd_; q[tail++] = w; cnt++; }
            }
        } else {
            int u = v - PN, j = u / N, y = u % N;
            for (int t = 0; t < ND; t++) {
                if (DT[t].j != j) continue;
                int w = DT[t].i * N + gmul(y, DT[t].gi);
                if (dist[w] < 0) { dist[w] = nd_; q[tail++] = w; cnt++; }
            }
        }
    }
    return cnt;
}

/* Unreached (representative, vertex) pairs. Zero iff the lift has diameter <= D. */
static long cost(void) {
    long V = 2L * P * N, bad = 0;
    for (int i = 0; i < P; i++) bad += V - reach_from(i * N);
    for (int j = 0; j < P; j++) bad += V - reach_from(P * N + j * N);
    return bad;
}

/* Simulated annealing on the voltages. Returns 1 if the cost reaches zero. */
static int anneal(long steps, double until) {
    long cur = cost();
    if (cur == 0) return 1;
    double T0 = 2.0, T1 = 0.1;
    for (long s = 0; s < steps; s++) {
        if ((s & 31) == 0 && now() > until) return 0;
        double T = T0 * pow(T1 / T0, (double)s / (double)steps);
        int t = rndint(ND);
        int g = rndint(N);
        int old = DT[t].g;
        if (g == old || clash(t, g)) continue;
        set_volt(t, g);
        long nc = cost();
        if (nc <= cur || rnd01() < exp((double)(cur - nc) / T)) {
            cur = nc;
            if (cur == 0) return 1;
        } else {
            set_volt(t, old);
        }
    }
    return 0;
}

/* Explicit check of the current lift: simple, d-regular, bipartite, diameter <= D. */
static int ADJ[MAXV][MAXD];
static int DEG[MAXV];
static int QB[MAXV], DB[MAXV];

static int full_check(void) {
    int V = 2 * P * N, PN = P * N;
    if (V <= 0 || V > MAXV) return 0;
    for (int v = 0; v < V; v++) DEG[v] = 0;
    for (int t = 0; t < ND; t++)
        for (int x = 0; x < N; x++) {
            int a = DT[t].i * N + x;
            int b = PN + DT[t].j * N + gmul(x, DT[t].g);
            if (DEG[a] >= d || DEG[b] >= d) return 0;
            ADJ[a][DEG[a]++] = b;
            ADJ[b][DEG[b]++] = a;
        }
    for (int v = 0; v < V; v++) {
        if (DEG[v] != d) return 0;
        for (int i = 0; i < DEG[v]; i++)
            for (int j = 0; j < i; j++)
                if (ADJ[v][i] == ADJ[v][j]) return 0;
    }
    for (int src = 0; src < V; src++) {
        for (int v = 0; v < V; v++) DB[v] = -1;
        int head = 0, tail = 0;
        DB[src] = 0;
        QB[tail++] = src;
        while (head < tail) {
            int v = QB[head++];
            if (DB[v] >= D) continue;
            for (int i = 0; i < DEG[v]; i++) {
                int w = ADJ[v][i];
                if (DB[w] < 0) { DB[w] = DB[v] + 1; QB[tail++] = w; }
            }
        }
        if (tail != V) return 0;
    }
    return 1;
}

static void try_save(void) {
    int V = 2 * P * N;
    if (V <= bestn) return;
    if (!full_check()) return;
    bestn = V;
    bP = P; bN = N; bND = ND; bGM = GM; bGK = GK; bGR = GR;
    memcpy(bDT, DT, sizeof(Dart) * (size_t)ND);
}

static void print_fallback(void) {
    if (d >= 1 && d <= MAXD && D >= 2) {
        printf("%d %d\n", 2 * d, d * d);
        for (int a = 0; a < d; a++)
            for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
    } else {
        printf("0 0\n");
    }
}

static void print_best(void) {
    if (bestn == 0) { print_fallback(); return; }
    P = bP; N = bN; ND = bND;
    memcpy(DT, bDT, sizeof(Dart) * (size_t)ND);
    set_group(bGM, bGK, bGR);
    int PN = P * N;
    printf("%d %d\n", 2 * PN, ND * N);
    for (int t = 0; t < ND; t++)
        for (int x = 0; x < N; x++) {
            int a = DT[t].i * N + x;
            int b = PN + DT[t].j * N + gmul(x, DT[t].g);
            printf("%d %d\n", a, b);
        }
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 2) { print_fallback(); return 0; }

    long moore = moore_bound();
    while (now() < t_end) {
        long target = bestn == 0 ? 2L * d : bestn + 2;
        if (bestn > 0 && rndint(10) < 3) target += 2 * rndint(3);
        if (target > moore || target + 2 * MAXP > MAXV) break;
        int p = 1 + rndint(MAXP);
        long n = (target + 2 * p - 1) / (2 * p);
        if (n < d) n = d;
        if (n > MAXG || 2 * p * n > moore || 2 * p * n > MAXV) continue;
        P = p;
        N = (int)n;
        pick_group(N);
        init_attempt();
        double until = now() + 6.0;
        if (until > t_end) until = t_end;
        if (anneal(60000L / p, until)) try_save();
    }
    print_best();
    return 0;
}
'''


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}
    if not lib.is_valid(*best, d, D):
        best = (2, [(0, 1)]) if d >= 1 and D >= 1 else (1, [])
    if start is not None and D == 3:
        return best   # Moore / record construction already optimal or record for D = 3
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if d >= 2 and D >= 2 and budget > 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=None, timeout=budget + 8)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except (RuntimeError, ValueError):
            pass   # keep the valid fallback
    return best
