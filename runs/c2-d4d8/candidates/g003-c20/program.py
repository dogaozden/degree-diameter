"""Three-stage search for d-regular bipartite graphs with diameter at most D.

Stage 1 is the parent's bi-Cayley engine (one base vertex per side, metacyclic and PSL/PGL
groups). Stage 2 is the parent's voltage-lift engine (K = 2..4 base vertices per side over
metacyclic groups). Both stay as safe fallbacks.

Stage 3 is new. It is an unstructured local search on d-regular bipartite graphs. The state is a
pair of neighbour lists, and the cost is the number of ordered vertex pairs at distance more than D,
computed by bitset ball expansion. Moves are random double edge switches, accepted by simulated
annealing. Whenever the cost reaches 0 the graph is saved and grown by one vertex pair. The new
pair takes d disjoint edges (a_i, b_i) and rewires them to a new A-vertex and a new B-vertex, so
the graph stays d-regular and bipartite. The search starts from the best graph found so far when
it fits the A-first layout, and otherwise from K_{d,d}. Python keeps the largest valid graph.
"""
import itertools
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
    /* Priority schedule: PSL(2,11) (1320 vertices) first, then PGL(2,11) (2640), PSL(2,13) (2184), ... */
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

/* Lift state: K base vertices per side, E = d*K darts. Dart e = (Ai[e], Bj[e], Vg[e]). */
static int K, E;
static int Ai[MAXE], Bj[MAXE], Vg[MAXE];
static int Bl[MAXK][MAXD];
static int bd[MAXV], bq[MAXV];
static const double LT0 = 5.0, LT1 = 0.3;

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

static int anneal(double until, long iters) {
    random_state();
    long cur = cost();
    for (long it = 0; it < iters; it++) {
        if (cur == 0) return 1;
        if ((it & 255) == 0 && now() > until) return 0;
        double T = LT0 * pow(LT1 / LT0, (double)it / (double)iters);
        int e1 = rndint(E);
        if (rndint(2) == 0) {
            int old = Vg[e1];
            Vg[e1] = rndint(GN);
            long nc = cost();
            if (nc <= cur || rnd01() < exp((double)(cur - nc) / T)) cur = nc;
            else Vg[e1] = old;
        } else {
            int e2 = rndint(E);
            if (e2 == e1) continue;
            int tmp = Bj[e1]; Bj[e1] = Bj[e2]; Bj[e2] = tmp;
            long nc = cost();
            if (nc <= cur || rnd01() < exp((double)(cur - nc) / T)) cur = nc;
            else { tmp = Bj[e1]; Bj[e1] = Bj[e2]; Bj[e2] = tmp; }
        }
    }
    return cur == 0;
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
        for (int t = 1; t <= n; t++)
            if (n % t == 0 && nd < 64) divs[nd++] = t;
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
        double until = now() + 2.5;
        if (until > t_end) until = t_end;
        if (anneal(until, 25000)) {
            best_half = (long)k * GN;
            have = 1;
            bK = k; bm = m; bt = t; br = r;
            memcpy(bBj, Bj, sizeof(int) * E);
            memcpy(bVg, Vg, sizeof(int) * E);
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

ANNEAL_C = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 1600
#define MAXW 52
#define MAXD 8
#define MAXV (2 * MAXN)
#define CH 2000
#define AT0 8.0
#define AT1 0.4

static int d, D, capN;
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

/* Current graph: side A = vertices 0..N-1, side B = vertices N..2N-1. */
static int N, W;
static int nbA[MAXN][MAXD];   /* A-vertex -> B-indices (0..N-1) */
static int nbB[MAXN][MAXD];   /* B-index -> A-vertices (0..N-1) */
static int bestA[MAXN][MAXD];
static int bestN = 0;
static uint64_t Rb[2][MAXV][MAXW];
static char usedA[MAXN], usedB[MAXN];

typedef struct { int a1, t1, b1, a2, t2, b2, s1, s2; } Move;

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Ordered pairs (u, v) with dist(u, v) > D. Zero iff the graph is valid. */
static long evaluate(void) {
    int V = 2 * N;
    for (int v = 0; v < V; v++) {
        for (int w = 0; w < W; w++) Rb[0][v][w] = 0;
        Rb[0][v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int step = 0; step < D; step++) {
        int src = step & 1, dst = src ^ 1;
        for (int v = 0; v < V; v++) {
            uint64_t *out = Rb[dst][v];
            const uint64_t *self = Rb[src][v];
            for (int w = 0; w < W; w++) out[w] = self[w];
            if (v < N) {
                for (int t = 0; t < d; t++) {
                    const uint64_t *nb = Rb[src][N + nbA[v][t]];
                    for (int w = 0; w < W; w++) out[w] |= nb[w];
                }
            } else {
                int *row = nbB[v - N];
                for (int t = 0; t < d; t++) {
                    const uint64_t *nb = Rb[src][row[t]];
                    for (int w = 0; w < W; w++) out[w] |= nb[w];
                }
            }
        }
    }
    int fin = D & 1;
    long cost = 0;
    for (int v = 0; v < V; v++) {
        int pc = 0;
        for (int w = 0; w < W; w++) pc += popc64(Rb[fin][v][w]);
        cost += V - pc;
    }
    return cost;
}

static int has_nbA(int a, int b) {
    for (int t = 0; t < d; t++) if (nbA[a][t] == b) return 1;
    return 0;
}

static int find_nbB(int b, int a) {
    for (int s = 0; s < d; s++) if (nbB[b][s] == a) return s;
    return -1;
}

/* Double edge switch: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). Keeps regularity and simplicity. */
static int try_switch(Move *m) {
    int a1 = rndint(N), t1 = rndint(d), a2 = rndint(N), t2 = rndint(d);
    if (a1 == a2) return 0;
    int b1 = nbA[a1][t1], b2 = nbA[a2][t2];
    if (b1 == b2) return 0;
    if (has_nbA(a1, b2) || has_nbA(a2, b1)) return 0;
    int s1 = find_nbB(b1, a1), s2 = find_nbB(b2, a2);
    if (s1 < 0 || s2 < 0) return 0;
    nbA[a1][t1] = b2;
    nbA[a2][t2] = b1;
    nbB[b1][s1] = a2;
    nbB[b2][s2] = a1;
    m->a1 = a1; m->t1 = t1; m->b1 = b1;
    m->a2 = a2; m->t2 = t2; m->b2 = b2;
    m->s1 = s1; m->s2 = s2;
    return 1;
}

static void undo_switch(const Move *m) {
    nbA[m->a1][m->t1] = m->b1;
    nbA[m->a2][m->t2] = m->b2;
    nbB[m->b1][m->s1] = m->a1;
    nbB[m->b2][m->s2] = m->a2;
}

/* Insert one A-vertex and one B-vertex: remove d disjoint edges (a_i,b_i) and join a_i-newB, b_i-newA. */
static int grow(void) {
    if (N + 1 > MAXN) return 0;
    int ua[MAXD], ub[MAXD], ta[MAXD], cnt = 0;
    long tries = 0;
    while (cnt < d && tries < 2000000) {
        tries++;
        int a = rndint(N), t = rndint(d);
        int b = nbA[a][t];
        if (usedA[a] || usedB[b]) continue;
        usedA[a] = 1;
        usedB[b] = 1;
        ua[cnt] = a; ub[cnt] = b; ta[cnt] = t;
        cnt++;
    }
    int ok = (cnt == d);
    if (ok) {
        int newA = N, newB = N;
        for (int i = 0; i < cnt; i++) {
            int a = ua[i], b = ub[i];
            int s = find_nbB(b, a);
            nbA[a][ta[i]] = newB;
            nbB[b][s] = newA;
            nbA[newA][i] = b;
            nbB[newB][i] = a;
        }
        N++;
        W = (2 * N + 63) / 64;
    }
    for (int i = 0; i < cnt; i++) { usedA[ua[i]] = 0; usedB[ub[i]] = 0; }
    return ok;
}

static void save_best(void) {
    bestN = N;
    for (int a = 0; a < N; a++)
        for (int t = 0; t < d; t++) bestA[a][t] = nbA[a][t];
}

/* Read a d-regular bipartite start graph with side A = first half of the labels. Returns 1 on success. */
static int read_start(void) {
    long n = 0, m = 0;
    if (scanf("%ld %ld", &n, &m) != 2) return 0;
    if (n <= 0 || m <= 0 || (n & 1)) return 0;
    long Nin = n / 2;
    if (Nin < d || Nin > MAXN || m != Nin * d) return 0;
    static int ca[MAXN], cb[MAXN];
    memset(ca, 0, sizeof ca);
    memset(cb, 0, sizeof cb);
    for (long i = 0; i < m; i++) {
        long u, v;
        if (scanf("%ld %ld", &u, &v) != 2) return 0;
        if (u > v) { long tmp = u; u = v; v = tmp; }
        if (u < 0 || u >= Nin || v < Nin || v >= n) return 0;
        int a = (int)u, b = (int)(v - Nin);
        if (ca[a] >= d || cb[b] >= d) return 0;
        for (int t = 0; t < ca[a]; t++) if (nbA[a][t] == b) return 0;
        nbA[a][ca[a]++] = b;
        nbB[b][cb[b]++] = a;
    }
    N = (int)Nin;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit cap_n\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    capN = atoi(argv[5]);
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double t0 = now();
    t_end = t0 + limit * 0.92;
    if (d < 3 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }
    if (capN > MAXN) capN = MAXN;

    if (!read_start()) {
        N = d;
        for (int a = 0; a < N; a++)
            for (int t = 0; t < d; t++) {
                nbA[a][t] = t;
                nbB[a][t] = t;
            }
    }
    W = (2 * N + 63) / 64;

    static const double T0 = AT0, T1 = AT1;
    long cur = evaluate();
    int done = 0;
    while (!done && now() < t_end) {
        for (long it = 0; it < CH && now() < t_end; it++) {
            if (cur == 0) {
                if (N > bestN) save_best();
                if (N >= capN || !grow()) { done = 1; break; }
                cur = evaluate();
                continue;
            }
            double T = T0 * pow(T1 / T0, (double)it / (double)CH);
            Move mv;
            if (!try_switch(&mv)) continue;
            long nc = evaluate();
            if (nc <= cur || rnd01() < exp((double)(cur - nc) / T)) cur = nc;
            else undo_switch(&mv);
        }
    }
    if (cur == 0 && N > bestN) save_best();

    if (bestN == 0) { printf("0 0\n"); return 0; }
    long m = (long)bestN * d;
    printf("%d %ld\n", 2 * bestN, m);
    for (int a = 0; a < bestN; a++)
        for (int t = 0; t < d; t++)
            printf("%d %d\n", a, bestN + bestA[a][t]);
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

    budget = 0.80 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 1.5:
        return best

    # Stage 1: parent bi-Cayley engine (fallback).
    b1 = 0.15 * budget
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(b1, 2)],
                         stdin_graph=None, timeout=b1 + 10)
        best = _keep_better(text, d, D, best)
    except Exception:
        pass

    # Stage 2: parent voltage-lift engine (fallback).
    b2 = 0.15 * budget
    if b2 > 1.0:
        half = max(1, best[0] // 2)
        cap = max(half, lib.moore_bound(d, D) // 2)
        try:
            text = lib.run_c(NEW_C, [d, D, seed, round(b2, 2), half, cap],
                             stdin_graph=None, timeout=b2 + 10)
            best = _keep_better(text, d, D, best)
        except Exception:
            pass

    # Stage 3: unstructured annealing with vertex-pair growth, seeded by the best graph so far.
    remaining = 0.80 * time_limit - 2.0 - (time.monotonic() - t0) - 0.5
    if remaining > 2.0:
        cap_n = min(1600, lib.moore_bound(d, D) // 2)
        start = best if best[0] >= 2 * d else None
        try:
            text = lib.run_c(ANNEAL_C, [d, D, seed, round(remaining, 2), cap_n],
                             stdin_graph=start, timeout=remaining + 10)
            best = _keep_better(text, d, D, best)
        except Exception:
            pass
    return best
