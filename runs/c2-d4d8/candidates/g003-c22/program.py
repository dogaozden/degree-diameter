"""Two-stage search for d-regular bipartite graphs with diameter at most D.

Stage 1 is the bi-Cayley engine (one base vertex per side, metacyclic and PSL/PGL groups).
It supplies a safe large fallback.

Stage 2 is a voltage lift with K = 2..4 base vertices per side over a metacyclic group
Z_m x| Z_t of order n, giving 2Kn vertices. Dart e = (Ai, Bj, Vg) joins A(i,x) to B(j, x*g)
for every x. Left multiplication by G is an automorphism, so diameter <= D iff BFS from
A(i,e) and B(j,e) reaches everything within D for every base index.

New in this version: iterated local search with best-state kicks. Each target size gets a
simulated-annealing descent, and when it stalls the search restores the best state found so
far, applies 1-3 random kicks (voltage change or B-side swap), and re-anneals at low
temperature. A kick is kept only as a new best if it lowers the cost, so progress accumulates
instead of being thrown away on restart. The target size grows whenever a lift is found.
Python keeps whichever valid graph is largest; the algebraic starts remain the fallback.
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

#define MAXG 2600
#define MAXD 8
#define CODEMAX 90000
#define GM_PGL 0
#define GM_PSL 1
#define GM_SEMI 2

typedef struct { int kind, q, m, k, r, n; } GroupSpec;

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

static long pw(long b, long e, long m) {
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

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

/* ---------- current group (multiplication table) ---------- */
static int kind_cur, qq, SEMI_m, SEMI_k, SEMI_r;
static int rp[MAXG];
static int invt[64];
static int gn, ID;
static int code_of[MAXG];
static int idx_of[CODEMAX];
static int INV[MAXG];
static uint16_t MT[MAXG * MAXG];
static int S[MAXD];

static void dec(int code, int *v) {
    v[3] = code % qq; code /= qq;
    v[2] = code % qq; code /= qq;
    v[1] = code % qq; code /= qq;
    v[0] = code;
}

static int enc4(const int *v) { return ((v[0] * qq + v[1]) * qq + v[2]) * qq + v[3]; }

/* Canonical code of a matrix class: PGL normalises the first nonzero entry to 1; PSL takes min(M, -M). */
static int canon(const int *v) {
    int w[4];
    if (kind_cur == GM_PGL) {
        int f = 1;
        for (int i = 0; i < 4; i++) if (v[i]) { f = v[i]; break; }
        int inv = invt[f];
        for (int i = 0; i < 4; i++) w[i] = v[i] * inv % qq;
        return enc4(w);
    }
    int neg[4];
    for (int i = 0; i < 4; i++) neg[i] = (qq - v[i]) % qq;
    int a = enc4(v), b = enc4(neg);
    return a < b ? a : b;
}

static int mul_code(int x, int y) {
    if (kind_cur == GM_SEMI) {
        int a = x / SEMI_k, b = x % SEMI_k, c = y / SEMI_k, e = y % SEMI_k;
        int na = (int)(((long)a + (long)rp[b] * c) % SEMI_m);
        return na * SEMI_k + (b + e) % SEMI_k;
    }
    int A[4], B[4], P[4];
    dec(x, A);
    dec(y, B);
    P[0] = (A[0] * B[0] + A[1] * B[2]) % qq;
    P[1] = (A[0] * B[1] + A[1] * B[3]) % qq;
    P[2] = (A[2] * B[0] + A[3] * B[2]) % qq;
    P[3] = (A[2] * B[1] + A[3] * B[3]) % qq;
    return canon(P);
}

static int build_group(const GroupSpec *gs) {
    kind_cur = gs->kind;
    for (int c = 0; c < CODEMAX; c++) idx_of[c] = -1;
    gn = 0;
    if (kind_cur == GM_SEMI) {
        SEMI_m = gs->m; SEMI_k = gs->k; SEMI_r = gs->r;
        if (SEMI_m < 1 || SEMI_k < 1 || SEMI_m * SEMI_k != gs->n || gs->n > MAXG) return 0;
        rp[0] = 1 % SEMI_m;
        for (int b = 1; b < SEMI_k; b++) rp[b] = (int)((long)rp[b - 1] * SEMI_r % SEMI_m);
        gn = gs->n;
        for (int c = 0; c < gn; c++) { code_of[c] = c; idx_of[c] = c; }
        ID = 0;
    } else {
        qq = gs->q;
        if (qq < 3 || qq > 17) return 0;
        for (int x = 1; x < qq; x++) invt[x] = (int)pw(x, qq - 2, qq);
        int total = qq * qq * qq * qq;
        for (int code = 0; code < total; code++) {
            int v[4];
            dec(code, v);
            int det = ((v[0] * v[3] - v[1] * v[2]) % qq + qq) % qq;
            if (kind_cur == GM_PGL ? det == 0 : det != 1) continue;
            if (canon(v) != code) continue;
            if (gn >= MAXG) return 0;
            code_of[gn] = code;
            idx_of[code] = gn;
            gn++;
        }
        if (gn != gs->n) return 0;
        int I[4] = {1, 0, 0, 1};
        ID = idx_of[canon(I)];
    }
    for (int i = 0; i < gn; i++)
        for (int j = 0; j < gn; j++)
            MT[(size_t)i * gn + j] = (uint16_t)idx_of[mul_code(code_of[i], code_of[j])];
    for (int i = 0; i < gn; i++)
        for (int j = 0; j < gn; j++)
            if (MT[(size_t)i * gn + j] == ID) { INV[i] = j; break; }
    return 1;
}

/* ---------- search ---------- */
static int bd[2 * MAXG], bq[2 * MAXG];

/* Number of vertices within distance D of src (src < gn: A-side, else B-side). */
static int reach_count(int src) {
    int V = 2 * gn;
    for (int v = 0; v < V; v++) bd[v] = -1;
    int head = 0, tail = 0;
    bd[src] = 0;
    bq[tail++] = src;
    while (head < tail) {
        int v = bq[head++];
        int dv = bd[v];
        if (dv >= D) continue;
        if (v < gn) {
            const uint16_t *row = MT + (size_t)v * gn;
            for (int i = 0; i < d; i++) {
                int u = gn + row[S[i]];
                if (bd[u] < 0) { bd[u] = dv + 1; bq[tail++] = u; }
            }
        } else {
            const uint16_t *row = MT + (size_t)(v - gn) * gn;
            for (int i = 0; i < d; i++) {
                int u = row[INV[S[i]]];
                if (bd[u] < 0) { bd[u] = dv + 1; bq[tail++] = u; }
            }
        }
    }
    return V - tail;
}

static int evaluate(void) { return reach_count(ID) + reach_count(gn + ID); }

static int in_first(int g, int cnt) {
    for (int i = 0; i < cnt; i++) if (S[i] == g) return 1;
    return 0;
}

static int search_group(double until, int *out) {
    int N = gn;
    if (N <= d) return 0;
    while (now() < until) {
        for (int i = 0; i < d; i++) {
            int g;
            do g = rndint(N); while (in_first(g, i));
            S[i] = g;
        }
        int f = evaluate();
        if (f == 0) { memcpy(out, S, sizeof(int) * d); return 1; }
        const int R = 30000;
        const double T0 = 1.5, T1 = 0.1;
        for (int it = 0; it < R; it++) {
            if ((it & 511) == 0 && now() > until) return 0;
            int i = rndint(d), old = S[i], g;
            do g = rndint(N); while (in_first(g, d));
            S[i] = g;
            int nf = evaluate();
            double T = T0 * pow(T1 / T0, (double)it / R);
            if (nf <= f || rnd01() < exp((double)(f - nf) / T)) f = nf;
            else S[i] = old;
            if (f == 0) { memcpy(out, S, sizeof(int) * d); return 1; }
        }
    }
    return 0;
}

/* Full independent check of the current S: every vertex must reach all others within D. */
static int full_check(void) {
    static int adj[2 * MAXG][MAXD];
    static int dist[2 * MAXG], qu[2 * MAXG];
    int N = gn, V = 2 * N;
    for (int g = 0; g < N; g++)
        for (int i = 0; i < d; i++) adj[g][i] = N + MT[(size_t)g * N + S[i]];
    for (int h = 0; h < N; h++)
        for (int i = 0; i < d; i++) adj[N + h][i] = MT[(size_t)h * N + INV[S[i]]];
    for (int src = 0; src < V; src++) {
        for (int v = 0; v < V; v++) dist[v] = -1;
        int head = 0, tail = 0;
        dist[src] = 0;
        qu[tail++] = src;
        while (head < tail) {
            int v = qu[head++];
            if (dist[v] >= D) continue;
            for (int i = 0; i < d; i++) {
                int u = adj[v][i];
                if (dist[u] < 0) { dist[u] = dist[v] + 1; qu[tail++] = u; }
            }
        }
        if (tail != V) return 0;
    }
    return 1;
}

static int best_n = 0;
static GroupSpec best_spec;
static int bestS[MAXD];

static int try_group(const GroupSpec *gs, double until) {
    if (!build_group(gs)) return 0;
    int out[MAXD];
    if (!search_group(until, out)) return 0;
    memcpy(S, out, sizeof(int) * d);
    if (!full_check()) return 0;
    best_n = 2 * gn;
    best_spec = *gs;
    memcpy(bestS, out, sizeof(int) * d);
    return 1;
}

/* Random metacyclic group Z_m x| Z_k with order in [483, 1300]. */
static int pick_semi(GroupSpec *gs) {
    for (int tries = 0; tries < 200000; tries++) {
        int k = 2 + rndint(40);
        int lo = (483 + k - 1) / k, hi = 1300 / k;
        if (hi < lo || hi < 3) continue;
        int m = lo + rndint(hi - lo + 1);
        if (m < 3) continue;
        int r = 2 + rndint(m - 2);
        if (gcd_i(r, m) != 1) continue;
        if (pw(r, k, m) != 1) continue;
        gs->kind = GM_SEMI; gs->q = 0; gs->m = m; gs->k = k; gs->r = r; gs->n = m * k;
        return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double t0 = now();
    t_end = t0 + limit * 0.93;
    if (d < 3 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    double total = t_end - now();
    /* Priority schedule: PSL(2,11) first, then PGL(2,11), PSL(2,13), ... */
    static const struct { int kind, q; double frac; } steps[] = {
        {GM_PSL, 11, 0.12}, {GM_PGL, 11, 0.45}, {GM_PSL, 13, 0.20},
        {GM_PGL, 13, 0.10}, {GM_PSL, 17, 0.10}};
    for (size_t s = 0; s < sizeof(steps) / sizeof(steps[0]); s++) {
        GroupSpec gs;
        memset(&gs, 0, sizeof gs);
        gs.kind = steps[s].kind;
        gs.q = steps[s].q;
        int q = gs.q;
        gs.n = (gs.kind == GM_PGL) ? q * (q * q - 1) : q * (q * q - 1) / 2;
        if (2 * gs.n <= best_n) continue;
        double tn = now();
        if (tn >= t_end) break;
        double until = tn + steps[s].frac * total;
        if (until > t_end) until = t_end;
        try_group(&gs, until);
    }
    while (now() < t_end) {
        if (best_n >= 2 * 1300) break;
        GroupSpec gs;
        memset(&gs, 0, sizeof gs);
        if (!pick_semi(&gs)) break;
        if (2 * gs.n <= best_n) continue;
        double until = now() + 1.5;
        if (until > t_end) until = t_end;
        try_group(&gs, until);
    }

    if (best_n == 0 || !build_group(&best_spec)) { printf("0 0\n"); return 0; }
    memcpy(S, bestS, sizeof(int) * d);
    int N = gn;
    long E = (long)N * d;
    printf("%d %ld\n", 2 * N, E);
    for (int g = 0; g < N; g++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", g, N + MT[(size_t)g * N + S[i]]);
    return 0;
}
'''

NEW_C = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 2048
#define MAXK 6
#define MAXD 8
#define MAXE (MAXK * MAXD)
#define MAXV (2 * MAXK * MAXN)
#define DUPW 40
#define BIGC 0x3fffffffffffffffL

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

static long pw(long b, long e, long m) {
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

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

/* Group Z_m x|_r Z_t, element a*t+b, (a,b)(c,e) = (a + r^b c, b + e). Identity is code 0. */
static int GM, GT, GR, GN;
static int rp[MAXN];
static uint16_t MT[MAXN * MAXN];
static int INV[MAXN];

static void build_group(int m, int t, int r) {
    GM = m; GT = t; GR = r; GN = m * t;
    rp[0] = 1 % m;
    for (int b = 1; b < t; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < GN; x++) {
        int a1 = x / t, b1 = x % t;
        for (int y = 0; y < GN; y++) {
            int a2 = y / t, b2 = y % t;
            int na = (int)(((long)a1 + (long)rp[b1] * a2) % m);
            int nb = (b1 + b2) % t;
            MT[(size_t)x * GN + y] = (uint16_t)(na * t + nb);
        }
    }
    for (int x = 0; x < GN; x++)
        for (int y = 0; y < GN; y++)
            if (MT[(size_t)x * GN + y] == 0) { INV[x] = y; break; }
}

/* Lift state: K base vertices per side, E = d*K darts. Dart e = (Ai[e], Bj[e], Vg[e]).
   Ai[e] = e/d is fixed; every B block j receives exactly d darts (swaps preserve this). */
static int K, E;
static int Ai[MAXE], Bj[MAXE], Vg[MAXE];
static int Bl[MAXK][MAXD];
static int bd[MAXV], bq[MAXV];

static int bestBj[MAXE], bestVg[MAXE];
static long bestc;

/* Cost = unreachable pairs from the 2K base sources + duplicate-dart penalty. */
static long cost(void) {
    long dup = 0;
    for (int e = 0; e < E; e++)
        for (int f = e + 1; f < E; f++)
            if (Ai[e] == Ai[f] && Bj[e] == Bj[f] && Vg[e] == Vg[f]) dup++;
    int cnt[MAXK];
    memset(cnt, 0, sizeof cnt);
    for (int e = 0; e < E; e++) {
        int j = Bj[e];
        Bl[j][cnt[j]++] = e;
    }
    int KN = K * GN, V = 2 * KN;
    long total = 0;
    for (int s = 0; s < 2 * K; s++) {
        int side = s >= K ? 1 : 0;
        int base = s % K;
        int src = side * KN + base * GN;
        for (int v = 0; v < V; v++) bd[v] = -1;
        int head = 0, tail = 0;
        bd[src] = 0;
        bq[tail++] = src;
        while (head < tail) {
            int v = bq[head++];
            int dv = bd[v];
            if (dv >= D) continue;
            int sd = v / KN;
            int rem = v - sd * KN;
            int bb = rem / GN;
            int x = rem - bb * GN;
            if (sd == 0) {
                for (int t = 0; t < d; t++) {
                    int e = bb * d + t;
                    int y = MT[(size_t)x * GN + Vg[e]];
                    int u = KN + Bj[e] * GN + y;
                    if (bd[u] < 0) { bd[u] = dv + 1; bq[tail++] = u; }
                }
            } else {
                for (int t = 0; t < d; t++) {
                    int e = Bl[bb][t];
                    int xx = MT[(size_t)x * GN + INV[Vg[e]]];
                    int u = Ai[e] * GN + xx;
                    if (bd[u] < 0) { bd[u] = dv + 1; bq[tail++] = u; }
                }
            }
        }
        total += V - tail;
    }
    return total + dup * DUPW;
}

static void random_state(void) {
    for (int e = 0; e < E; e++) {
        Ai[e] = e / d;
        Bj[e] = e / d;
        Vg[e] = rndint(GN);
    }
    for (int e = E - 1; e > 0; e--) {
        int f = rndint(e + 1);
        int tmp = Bj[e]; Bj[e] = Bj[f]; Bj[f] = tmp;
    }
}

static void save_best(long c) {
    bestc = c;
    memcpy(bestBj, Bj, sizeof(int) * E);
    memcpy(bestVg, Vg, sizeof(int) * E);
}

static void load_best(void) {
    memcpy(Bj, bestBj, sizeof(int) * E);
    memcpy(Vg, bestVg, sizeof(int) * E);
}

/* Simulated annealing from the current state; tracks the global best (bestc). */
static long sa_run(double until, long iters, double Ta, double Tb) {
    long cur = cost();
    if (cur < bestc) save_best(cur);
    for (long it = 0; it < iters && bestc > 0; it++) {
        if ((it & 127) == 0 && now() > until) break;
        double T = Ta * pow(Tb / Ta, (double)it / (double)iters);
        int e1 = rndint(E);
        int kind = rndint(2);
        int e2 = -1, oldv = 0;
        if (kind == 0) {
            oldv = Vg[e1];
            Vg[e1] = rndint(GN);
        } else {
            e2 = rndint(E);
            if (e2 == e1) continue;
            int tmp = Bj[e1]; Bj[e1] = Bj[e2]; Bj[e2] = tmp;
        }
        long nc = cost();
        if (nc <= cur || rnd01() < exp((double)(cur - nc) / T)) {
            cur = nc;
            if (cur < bestc) save_best(cur);
        } else if (kind == 0) {
            Vg[e1] = oldv;
        } else {
            int tmp = Bj[e1]; Bj[e1] = Bj[e2]; Bj[e2] = tmp;
        }
    }
    return bestc;
}

/* New routine: iterated local search. After an initial anneal, repeatedly restore the best
   state, kick it with 1-3 random moves, and re-anneal at low temperature. Only improvements
   replace the best state, so accumulated progress is never discarded. */
static int solve_lift(double until) {
    random_state();
    bestc = BIGC;
    sa_run(until, 25000, 5.0, 0.3);
    while (bestc > 0 && now() < until) {
        load_best();
        int kicks = 1 + rndint(3);
        for (int k = 0; k < kicks; k++) {
            if (rndint(2)) {
                Vg[rndint(E)] = rndint(GN);
            } else {
                int a = rndint(E), b = rndint(E);
                int tmp = Bj[a]; Bj[a] = Bj[b]; Bj[b] = tmp;
            }
        }
        sa_run(until, 3000, 0.6, 0.15);
    }
    return bestc == 0;
}

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: %s d D seed time_limit start_half cap_half\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long start_half = atol(argv[5]);
    long cap_half = atol(argv[6]);
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double t0 = now();
    t_end = t0 + limit * 0.93;
    if (d < 3 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }
    if (cap_half > (long)MAXN * MAXK) cap_half = (long)MAXN * MAXK;

    long best_half = start_half;
    int have = 0;
    int bK = 0, bm = 0, bt = 0, br = 0;
    static int bBj[MAXE], bVg[MAXE];

    while (now() < t_end) {
        if (best_half + 1 > cap_half) break;
        int k = 2 + rndint(3);                       /* K in {2,3,4} */
        long Tg = best_half + 1 + best_half / 40;   /* aim about 2.5% above the best so far */
        if (Tg > cap_half) Tg = cap_half;
        long nlo = (Tg + k - 1) / k;
        long nl = nlo + rndint(4);
        if (nl < 3 || nl > MAXN) continue;
        int n = (int)nl;
        if ((long)k * n > cap_half) n = (int)(cap_half / k);
        if (n < 3 || n > MAXN) continue;
        if ((long)k * n <= best_half) continue;

        int divs[64];
        int nd = 0;
        for (int tt = 1; tt <= n; tt++)
            if (n % tt == 0 && nd < 64) divs[nd++] = tt;
        int t = divs[rndint(nd)];
        int m = n / t;
        int r = (m > 1) ? 1 : 0;
        if (m > 1) {
            for (int tr = 0; tr < 300; tr++) {
                int cand = 1 + rndint(m - 1);
                if (gcd_i(cand, m) == 1 && pw(cand, t, m) == 1 % m) { r = cand; break; }
            }
        }
        build_group(m, t, r);
        K = k;
        E = d * K;
        double until = now() + 4.0;
        if (until > t_end) until = t_end;
        if (solve_lift(until)) {
            best_half = (long)k * GN;
            have = 1;
            bK = k; bm = m; bt = t; br = r;
            memcpy(bBj, bestBj, sizeof(int) * E);
            memcpy(bVg, bestVg, sizeof(int) * E);
        }
    }

    if (!have) { printf("0 0\n"); return 0; }
    build_group(bm, bt, br);
    K = bK;
    E = d * K;
    for (int e = 0; e < E; e++) {
        Ai[e] = e / d;
        Bj[e] = bBj[e];
        Vg[e] = bVg[e];
    }
    int KN = K * GN;
    long cnt = (long)E * GN;
    printf("%d %ld\n", 2 * KN, cnt);
    for (int e = 0; e < E; e++)
        for (int x = 0; x < GN; x++) {
            int a = Ai[e] * GN + x;
            int b = KN + Bj[e] * GN + MT[(size_t)x * GN + Vg[e]];
            printf("%d %d\n", a, b);
        }
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


def _keep_better(text, d, D, best):
    """Return the parsed graph from C text if it is valid and larger than best, else best."""
    try:
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            return (n, e)
    except Exception:
        pass
    return best


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    # Safe fallback: K_{d,d} or the best algebraic start.
    best = lib.haar_graph(d, range(d))
    for n, e in known_starts(d, D):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 8 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 1.5:
        return best

    # Stage 1: parent bi-Cayley engine (secures a large fallback).
    b1 = 0.20 * budget
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(b1, 2)],
                         stdin_graph=None, timeout=b1 + 10)
        best = _keep_better(text, d, D, best)
    except Exception:
        pass

    # Stage 2: iterated-local-search voltage lifts over metacyclic groups.
    b2 = budget - b1 - 1.0
    if b2 > 1.0:
        half = max(1, best[0] // 2)
        cap = max(half, lib.moore_bound(d, D) // 2)
        try:
            text = lib.run_c(NEW_C, [d, D, seed, round(b2, 2), half, cap],
                             stdin_graph=None, timeout=b2 + 10)
            best = _keep_better(text, d, D, best)
        except Exception:
            pass
    return best
