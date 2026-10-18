"""Combined multi-orbit affine and semidirect lifts for the bipartite degree-diameter problem.

Merges two parent ideas:
- Multi-orbit lifts with B in {1, 2, 3} orbits per side (parent g006-c09). Each dart
  slot gets a random permutation of the orbits, so every d-regular base on B+B
  vertices is covered. Left translations are automorphisms, so BFS from the 2B orbit
  representatives decides the diameter.
- Repeated randomized attempts over candidate orders (parent g006-c10).

New in this version: the group family is widened. Besides the affine groups
F_q x| H (q a prime power, H of order c dividing q-1), the C engine also searches
semidirect products Z_m x|_r Z_k, which include cyclic (k = 1) and abelian (r = 1)
groups. Candidates are generated for each orbit count B, sorted by order, and
scheduled in two phases. A binary search finds a feasible region per B. A round-robin
sweep then tries only candidates whose total 2*B*N beats the current best.

The C engine returns a valid graph or "0 0". Python checks every result with
lib.is_valid and keeps a valid fallback (K_{d,d}, or a projective-plane or
generalized-quadrangle graph when one applies).
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Combined multi-orbit lift search over affine and semidirect groups.
 * Usage: prog d D seed time_limit lo3 hi3 lo2 hi2 lo1 hi1
 * Output: "n m" then m lines "u v", or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXQ 256
#define MAXC 256
#define MAXN 4800
#define MAXD 32
#define MAXB 3

typedef struct { int type, q, p, k, c, m, kk, r, N; } Cand;

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
static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

/* ------------------------------------------------------------ finite fields */

static int ADDT[MAXQ][MAXQ], MULT[MAXQ][MAXQ], NEGT[MAXQ];
static int built_q = -1;

static int factor_pp(int q, int *p, int *k) {
    int pp = 0;
    for (int f = 2; f * f <= q; f++)
        if (q % f == 0) { pp = f; break; }
    if (!pp) pp = q;
    int r = q, kk = 0;
    while (r % pp == 0) { r /= pp; kk++; }
    if (r != 1 || kk < 1) return 0;
    *p = pp;
    *k = kk;
    return 1;
}

static int polymul(int a, int b, int p, int k, const int *pw, const int *m) {
    int pa[16], pb[16], prod[32];
    for (int i = 0; i < k; i++) {
        pa[i] = (a / pw[i]) % p;
        pb[i] = (b / pw[i]) % p;
    }
    for (int i = 0; i < 2 * k; i++) prod[i] = 0;
    for (int i = 0; i < k; i++)
        for (int j = 0; j < k; j++)
            prod[i + j] = (prod[i + j] + pa[i] * pb[j]) % p;
    for (int deg = 2 * k - 2; deg >= k; deg--) {
        int c = prod[deg];
        if (!c) continue;
        for (int i = 0; i < k; i++) {
            int idx = deg - k + i;
            prod[idx] = ((prod[idx] - c * m[i]) % p + p) % p;
        }
        prod[deg] = 0;
    }
    int r = 0;
    for (int i = 0; i < k; i++) r += prod[i] * pw[i];
    return r;
}

static void build_field(int q, int p, int k) {
    if (built_q == q) return;
    int pw[16];
    pw[0] = 1;
    for (int i = 1; i <= k; i++) pw[i] = pw[i - 1] * p;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++) {
            int r = 0;
            for (int i = 0; i < k; i++)
                r += (((a / pw[i]) % p + (b / pw[i]) % p) % p) * pw[i];
            ADDT[a][b] = r;
        }
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++)
            if (ADDT[a][b] == 0) NEGT[a] = b;

    int found = 0;
    for (int code = 0; code < q && !found; code++) {
        int m[16];
        int t = code;
        for (int i = 0; i < k; i++) { m[i] = t % p; t /= p; }
        int ok = 1;
        for (int a = 1; a < q && ok; a++)
            for (int b = 1; b < q && ok; b++)
                if (polymul(a, b, p, k, pw, m) == 0) ok = 0;
        if (ok) {
            found = 1;
            for (int a = 0; a < q; a++)
                for (int b = 0; b < q; b++)
                    MULT[a][b] = polymul(a, b, p, k, pw, m);
        }
    }
    built_q = q;
}

/* ------------------------------------------------------------ groups */

/* GT = 0: affine F_q x| H, element (a, h_j) coded a*GC + j.
 * GT = 1: semidirect Z_SM x|_SR Z_SK, element (a, b) coded a*SK + b,
 *         product (a, b)(c, e) = (a + r^b c, b + e). Cyclic: SK = 1. */
static int GT = 0;
static int GQ, GC, GN;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];
static int SM, SK, SR;
static int SPW[MAXN];

static void setup_affine(int q, int p, int k, int c) {
    build_field(q, p, k);
    GT = 0;
    GQ = q;
    GC = c;
    GN = q * c;
    int g = -1;
    for (int g0 = 2; g0 < q && g < 0; g0++) {
        int x = 1, ord = 0;
        do { x = MULT[x][g0]; ord++; } while (x != 1 && ord < q);
        if (ord == q - 1) g = g0;
    }
    PWG[0] = 1;
    for (int i = 1; i < q - 1; i++) PWG[i] = MULT[PWG[i - 1]][g];
    int step = (q - 1) / c;
    for (int j = 0; j < q; j++) hidx[j] = -1;
    for (int t = 0; t < c; t++) {
        Hel[t] = PWG[(t * step) % (q - 1)];
        hidx[Hel[t]] = t;
    }
    for (int j = 0; j < c; j++)
        for (int t = 0; t < c; t++)
            HM[j * c + t] = hidx[MULT[Hel[j]][Hel[t]]];
}

static void setup_semi(int m, int kk, int r) {
    GT = 1;
    SM = m;
    SK = kk;
    SR = r;
    GN = m * kk;
    GQ = 0;
    GC = 1;
    SPW[0] = 1 % m;
    for (int b = 1; b < kk; b++) SPW[b] = (SPW[b - 1] * r) % m;
}

static void setup_cand(const Cand *cd) {
    if (cd->type == 0) setup_affine(cd->q, cd->p, cd->k, cd->c);
    else setup_semi(cd->m, cd->kk, cd->r);
}

static inline int gmul(int x, int y) {
    if (GT == 1) {
        int a = x / SK, b = x % SK, c = y / SK, e = y % SK;
        int na = (a + SPW[b] * c) % SM;
        return na * SK + (b + e) % SK;
    }
    int a = x / GC, j = x % GC, b = y / GC, t = y % GC;
    int na = ADDT[a][MULT[Hel[j]][b]];
    return na * GC + HM[j * GC + t];
}

static inline int ginv(int x) {
    if (GT == 1) {
        int a = x / SK, b = x % SK;
        int nb = (SK - b) % SK;
        int na = (SM - (SPW[nb] * a) % SM) % SM;
        return na * SK + nb;
    }
    int a = x / GC, j = x % GC;
    int jn = (GC - j) % GC;
    int na = NEGT[MULT[Hel[jn]][a]];
    return na * GC + jn;
}

/* ------------------------------------------------------------ multi-orbit lift state */

static int curB;
static int tgt[MAXB][MAXD], vol[MAXB][MAXD];
static int fw[MAXB][MAXD][MAXN], bw[MAXB][MAXD][MAXN];
static int incI[MAXB][MAXD], incT[MAXB][MAXD];
static int vis[2 * MAXB * MAXN], que[2 * MAXB * MAXN];
static int stamp_ = 0;

static int bestTotal = 0, bestB = 0;
static Cand bestCand;
static int bestTgt[MAXB][MAXD], bestVol[MAXB][MAXD];

static int base_connected(int B) {
    int seenL[MAXB], seenR[MAXB];
    for (int i = 0; i < B; i++) { seenL[i] = 0; seenR[i] = 0; }
    seenL[0] = 1;
    int changed = 1;
    while (changed) {
        changed = 0;
        for (int i = 0; i < B; i++)
            for (int t = 0; t < d; t++) {
                int j = tgt[i][t];
                if (seenL[i] && !seenR[j]) { seenR[j] = 1; changed = 1; }
                if (seenR[j] && !seenL[i]) { seenL[i] = 1; changed = 1; }
            }
    }
    for (int i = 0; i < B; i++)
        if (!seenL[i] || !seenR[i]) return 0;
    return 1;
}

static int set_incidence(int B) {
    int cnt[MAXB];
    for (int j = 0; j < B; j++) cnt[j] = 0;
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) {
            int j = tgt[i][t];
            if (j < 0 || j >= B || cnt[j] >= d) return 0;
            incI[j][cnt[j]] = i;
            incT[j][cnt[j]] = t;
            cnt[j]++;
        }
    for (int j = 0; j < B; j++)
        if (cnt[j] != d) return 0;
    return 1;
}

static void random_pattern(int B) {
    curB = B;
    for (;;) {
        for (int t = 0; t < d; t++) {
            int p[MAXB];
            for (int i = 0; i < B; i++) p[i] = i;
            for (int i = B - 1; i > 0; i--) {
                int r = rndint(i + 1);
                int tmp = p[i]; p[i] = p[r]; p[r] = tmp;
            }
            for (int i = 0; i < B; i++) tgt[i][t] = p[i];
        }
        if (base_connected(B) && set_incidence(B)) break;
    }
}

static int valid_value(int i, int t, int x, int limit) {
    for (int t2 = 0; t2 < limit; t2++)
        if (t2 != t && tgt[i][t2] == tgt[i][t] && vol[i][t2] == x) return 0;
    return 1;
}

static int simple_state(int B) {
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++)
            for (int t2 = 0; t2 < t; t2++)
                if (tgt[i][t2] == tgt[i][t] && vol[i][t2] == vol[i][t]) return 0;
    return 1;
}

static void set_dart(int i, int t, int x) {
    vol[i][t] = x;
    int xi = ginv(x);
    for (int g = 0; g < GN; g++) {
        fw[i][t][g] = gmul(g, x);
        bw[i][t][g] = gmul(g, xi);
    }
}

/* Number of vertices within distance D of src. */
static int bfs_count(int src) {
    int N = GN, BN = curB * N;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < BN) {
                int i = v / N, g = v % N;
                for (int t = 0; t < d; t++) {
                    int u = BN + tgt[i][t] * N + fw[i][t][g];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - BN, j = w / N, x = w % N;
                for (int k = 0; k < d; k++) {
                    int i = incI[j][k], t = incT[j][k];
                    int u = i * N + bw[i][t][x];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

static long cover_cost(void) {
    int N = GN, V = 2 * curB * N;
    long cost = 0;
    for (int i = 0; i < curB; i++) cost += (long)(V - bfs_count(i * N));
    for (int j = 0; j < curB; j++) cost += (long)(V - bfs_count((curB + j) * N));
    return cost;
}

/* Simulated annealing over voltages with random base patterns.
 * Returns 1 with a simple cost-0 state in tgt/vol, 0 on timeout. */
static int search_group(int B, double until) {
    int N = GN;
    const int iters = 8000;
    curB = B;
    while (now() < until) {
        random_pattern(B);
        for (int i = 0; i < B; i++)
            for (int t = 0; t < d; t++) {
                int x, tries = 0;
                do { x = rndint(N); tries++; } while (!valid_value(i, t, x, t) && tries < 100000);
                set_dart(i, t, x);
            }
        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int i = rndint(B), t = rndint(d);
            int x, tries = 0;
            do { x = rndint(N); tries++; } while (!valid_value(i, t, x, d) && tries < 1000);
            if (tries >= 1000) continue;
            int old = vol[i][t];
            set_dart(i, t, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_dart(i, t, old);
            }
        }
        if (cost == 0 && simple_state(B)) return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ candidate families */

static Cand *arr_buf = NULL;
static int arr_n = 0, arr_cap = 0;
static Cand *famArr[MAXB + 1];
static int famCnt[MAXB + 1];

static void push_cand(const Cand *cd) {
    if (arr_n == arr_cap) {
        int nc = arr_cap ? arr_cap * 2 : 256;
        Cand *t = realloc(arr_buf, sizeof(Cand) * (size_t)nc);
        if (!t) return;
        arr_buf = t;
        arr_cap = nc;
    }
    arr_buf[arr_n++] = *cd;
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = (const Cand *)a, *y = (const Cand *)b;
    if (x->N != y->N) return x->N < y->N ? -1 : 1;
    return 0;
}

/* Affine candidates F_q x| H (q < MAXQ) and semidirect Z_m x|_r Z_k (all valid r, with
 * order-of-r dividing k), restricted to orders in [lo, hi]. */
static void gen_family(int B, int lo, int hi) {
    arr_buf = NULL;
    arr_n = 0;
    arr_cap = 0;
    famArr[B] = NULL;
    famCnt[B] = 0;
    if (lo > hi) return;
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 2; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            long N = (long)q * c;
            if (N < lo || N > hi) continue;
            Cand cd = {0, q, p, k, c, 0, 0, 0, (int)N};
            push_cand(&cd);
        }
    }
    for (int m = 2; m <= hi; m++) {
        int kmax = hi / m;
        if (kmax < 1) break;
        int kmin = (lo + m - 1) / m;
        if (kmin < 1) kmin = 1;
        if (kmin > kmax) continue;
        for (int r = 1; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            int e = 0;
            long x = r;
            for (int j = 1; j <= kmax; j++) {
                if (x == 1 % m) { e = j; break; }
                x = (x * r) % m;
            }
            if (!e) continue;
            int kk0 = ((kmin + e - 1) / e) * e;
            for (int kk = kk0; kk <= kmax; kk += e) {
                Cand cd = {1, 0, 0, 0, 0, m, kk, r, m * kk};
                push_cand(&cd);
            }
        }
    }
    if (arr_n > 1) qsort(arr_buf, (size_t)arr_n, sizeof(Cand), cmp_cand);
    famArr[B] = arr_buf;
    famCnt[B] = arr_n;
    arr_buf = NULL;
    arr_n = 0;
    arr_cap = 0;
}

static void record(int B, const Cand *cd) {
    int total = 2 * B * cd->N;
    if (total <= bestTotal) return;
    bestTotal = total;
    bestB = B;
    bestCand = *cd;
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) {
            bestTgt[i][t] = tgt[i][t];
            bestVol[i][t] = vol[i][t];
        }
}

/* Binary search over the sorted family for a feasible order. */
static void binary_phase(int B, double until) {
    int n = famCnt[B];
    if (n == 0) return;
    Cand *arr = famArr[B];
    int a = 0, b = n - 1;
    while (a <= b) {
        double tnow = now();
        if (tnow >= until) break;
        int mid = (a + b) / 2;
        const Cand *cd = &arr[mid];
        if (2 * B * cd->N <= bestTotal) { a = mid + 1; continue; }
        double rem = until - tnow;
        double slice = 0.3 * rem;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        setup_cand(cd);
        if (search_group(B, now() + slice)) {
            record(B, cd);
            a = mid + 1;
        } else {
            b = mid - 1;
        }
    }
}

/* Round-robin ascending sweep over eligible candidates (total above the best),
 * with fresh random restarts on every pass. */
static void sweep_phase(double until) {
    int ordB[3] = {3, 2, 1};
    int ptr[MAXB + 1];
    for (int B = 0; B <= MAXB; B++) ptr[B] = 0;
    for (;;) {
        int attempted = 0;
        for (int oi = 0; oi < 3; oi++) {
            int B = ordB[oi];
            int n = famCnt[B];
            if (n == 0) continue;
            Cand *arr = famArr[B];
            while (ptr[B] < n && 2 * B * arr[ptr[B]].N <= bestTotal) ptr[B]++;
            if (ptr[B] >= n) {
                ptr[B] = 0;
                while (ptr[B] < n && 2 * B * arr[ptr[B]].N <= bestTotal) ptr[B]++;
                if (ptr[B] >= n) continue;
            }
            double rem = until - now();
            if (rem < 0.5) return;
            double slice = 0.1 * rem;
            if (slice < 1.0) slice = 1.0;
            if (slice > rem) slice = rem;
            setup_cand(&arr[ptr[B]]);
            if (search_group(B, now() + slice)) record(B, &arr[ptr[B]]);
            ptr[B]++;
            attempted = 1;
        }
        if (!attempted) return;
    }
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 11) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo[MAXB + 1], hi[MAXB + 1];
    lo[3] = atoi(argv[5]); hi[3] = atoi(argv[6]);
    lo[2] = atoi(argv[7]); hi[2] = atoi(argv[8]);
    lo[1] = atoi(argv[9]); hi[1] = atoi(argv[10]);
    double t0 = now();
    t_end = t0 + limit * 0.95 - 0.8;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    for (int B = 1; B <= MAXB; B++) {
        if (hi[B] > MAXN - 1) hi[B] = MAXN - 1;
        if (lo[B] < 2 * d) lo[B] = 2 * d;
        gen_family(B, lo[B], hi[B]);
    }
    double span = t_end - t0;
    if (span < 2.0) {
        printf("0 0\n");
        return 0;
    }

    /* Phase 1: binary search per family, in the order B = 3, 2, 1. */
    const double shares[MAXB + 1] = {0.0, 0.13, 0.12, 0.15};
    int ordB[3] = {3, 2, 1};
    double cum = 0.0;
    for (int oi = 0; oi < 3; oi++) {
        int B = ordB[oi];
        cum += shares[B];
        binary_phase(B, t0 + cum * span);
    }
    /* Phase 2: sweep eligible candidates until the time is up. */
    sweep_phase(t_end);

    if (bestTotal == 0) {
        printf("0 0\n");
        return 0;
    }

    /* Rebuild the best graph. */
    int B = bestB;
    setup_cand(&bestCand);
    curB = B;
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) tgt[i][t] = bestTgt[i][t];
    if (!set_incidence(B)) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) set_dart(i, t, bestVol[i][t]);

    int N = GN, BN = B * N, V = 2 * BN, E = BN * d;
    static int adj[2 * MAXB * MAXN][MAXD];
    for (int v = 0; v < BN; v++) {
        int i = v / N, g = v % N;
        for (int t = 0; t < d; t++) adj[v][t] = BN + tgt[i][t] * N + fw[i][t][g];
    }
    for (int w = BN; w < V; w++) {
        int j = (w - BN) / N, x = (w - BN) % N;
        for (int k = 0; k < d; k++) {
            int i = incI[j][k], t = incT[j][k];
            adj[w][k] = i * N + bw[i][t][x];
        }
    }

    /* Simplicity: no repeated neighbour anywhere. */
    for (int v = 0; v < V; v++)
        for (int k = 0; k < d; k++)
            for (int l = 0; l < k; l++)
                if (adj[v][k] == adj[v][l]) {
                    printf("0 0\n");
                    return 0;
                }

    /* Full distance check from every vertex when cheap. */
    if (V <= 5000) {
        for (int s = 0; s < V; s++) {
            stamp_++;
            int head = 0, tail = 0;
            que[tail++] = s;
            vis[s] = stamp_;
            for (int lvl = 0; lvl < D && head < tail; lvl++) {
                int end = tail;
                while (head < end) {
                    int v = que[head++];
                    for (int k = 0; k < d; k++) {
                        int u = adj[v][k];
                        if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                    }
                }
            }
            if (tail != V) {
                printf("0 0\n");
                return 0;
            }
        }
    }

    printf("%d %d\n", V, E);
    for (int v = 0; v < BN; v++)
        for (int t = 0; t < d; t++)
            printf("%d %d\n", v, adj[v][t]);
    return 0;
}
'''


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
    """W(q) for the largest prime power q with q + 1 <= d (kept small for speed)."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is valid for every D >= 2 and is the safe fallback.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        if cand is None:
            return
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        try:
            consider(_best_pg(d))
        except Exception:
            pass
        # Exact Moore graph: nothing can beat it.
        if D == 3 and lib.is_prime_power(d - 1) and best[0] > 2 * d:
            return best
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    if D == 4:
        try:
            consider(_best_gq(d))
        except Exception:
            pass

    # Combined search: B = 3 (6N vertices), B = 2 (4N), B = 1 (2N), affine and semidirect groups.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.88 * time_limit - (time.monotonic() - t0) - 3.0
        lo3 = max(2 * d, best[0] // 6 + 1, mb // 24)
        hi3 = mb // 6
        lo2 = max(2 * d, best[0] // 4 + 1, mb // 16)
        hi2 = mb // 4
        lo1 = max(2 * d, best[0] // 2 + 1, mb // 8)
        hi1 = mb // 2
        ranges_ok = lo3 <= hi3 or lo2 <= hi2 or lo1 <= hi1
        if budget > 4.0 and ranges_ok:
            try:
                text = lib.run_c(C_SOURCE,
                                 [d, D, seed, round(budget, 2),
                                  lo3, hi3, lo2, hi2, lo1, hi1],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
