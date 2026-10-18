"""Two engines for the bipartite degree-diameter problem, best result kept.

Stage 1 runs the two-orbit affine Haar lift engine (the previous champion) with
a reduced share of the time, so a strong safe graph is always available.

Stage 2 is the new, different construction. It uses B = 2, 3 or 4 orbits per
side over a metacyclic group Z_m x|_r Z_k, with a general voltage lift:

    dart (i, t) joins L_(i,g) to R_(sig[i][t], g * vol[i][t]),

where sig[.][t] is a random permutation of the B orbits for each t. Every right
orbit then gets exactly d darts, so the graph is d-regular and bipartite. Left
translations are automorphisms, so BFS from L_(i,e) and R_(j,e) decides the
diameter. Simulated annealing moves voltages and swaps pattern entries. The
order (2BN) is searched by bisection, starting above the best graph found so
far, so stage 2 only has to beat stage 1.

Every candidate is re-checked in C (simple graph, full BFS when small) and again
in Python with lib.is_valid. A valid fallback is always returned.
"""
import itertools
import time

import lib

PARENT_C = r'''
/* Two-orbit affine lifts.
 * Group G = F_q x| H, |G| = N = q*c with c >= 2 and c | q-1.
 * B orbits per side (B = 1 or 2). Left vertex (i,g) ~ right vertex (j, g*v)
 * for each dart (i,t) with tgt[i][t] = j and voltage v = vol[i][t].
 * B = 2 pattern: L0->R0 (a darts), L0->R1 (d-a), L1->R0 (d-a), L1->R1 (a), 1 <= a <= d/2.
 * Left translations are automorphisms, transitive on each orbit, so checking
 * BFS from L_(i,e) and R_(j,e) decides the diameter.
 * Usage: prog d D seed time_limit lo2 hi2 lo1 hi1
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
#define MAXB 2
#define MAXCAND 16384

typedef struct { int q, p, k, c, N; } Cand;

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

/* ------------------------------------------------------------ group G = F_q x| H */

static int GQ, GC, GN;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];

static void setup_group(int q, int p, int k, int c) {
    build_field(q, p, k);
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

static inline int gmul(int x, int y) {
    int a = x / GC, j = x % GC, b = y / GC, t = y % GC;
    int na = ADDT[a][MULT[Hel[j]][b]];
    return na * GC + HM[j * GC + t];
}

static int ginv(int x) {
    int a = x / GC, j = x % GC;
    int jn = (GC - j) % GC;
    int na = NEGT[MULT[Hel[jn]][a]];
    return na * GC + jn;
}

/* ------------------------------------------------------------ two-orbit lift state */

static int curB, curA;
static int tgt[MAXB][MAXD], vol[MAXB][MAXD];
static int fw[MAXB][MAXD][MAXN], bw[MAXB][MAXD][MAXN];
static int incI[MAXB][2 * MAXD], incT[MAXB][2 * MAXD];
static int vis[2 * MAXB * MAXN], que[2 * MAXB * MAXN];
static int stamp_ = 0;

static int bestTotal = 0, bestB, bestA, bestN, bestQ, bestP, bestK, bestC;
static int bestVol[MAXB][MAXD];

/* Pattern: B = 1 puts all darts on R0; B = 2 uses parameter a (1 <= a <= d/2). */
static void set_pattern(int B, int a) {
    curB = B;
    curA = a;
    for (int t = 0; t < d; t++) {
        if (B == 1) {
            tgt[0][t] = 0;
        } else {
            tgt[0][t] = (t < a) ? 0 : 1;
            tgt[1][t] = (t < a) ? 1 : 0;
        }
    }
    for (int j = 0; j < B; j++) {
        int cnt = 0;
        for (int i = 0; i < B; i++)
            for (int t = 0; t < d; t++)
                if (tgt[i][t] == j) {
                    incI[j][cnt] = i;
                    incT[j][cnt] = t;
                    cnt++;
                }
    }
}

/* Voltage of dart (i,t) is x; fw maps L-coordinate g to R-coordinate g*x,
 * bw maps R-coordinate y to L-coordinate y*x^-1. */
static void set_dart(int i, int t, int x) {
    vol[i][t] = x;
    int xi = ginv(x);
    for (int g = 0; g < GN; g++) {
        fw[i][t][g] = gmul(g, x);
        bw[i][t][g] = gmul(g, xi);
    }
}

/* Darts of the same (i, target) class need distinct voltages so the graph is simple. */
static int valid_value(int i, int t, int x, int limit) {
    for (int t2 = 0; t2 < limit; t2++)
        if (t2 != t && tgt[i][t2] == tgt[i][t] && vol[i][t2] == x) return 0;
    return 1;
}

/* BFS up to depth D; returns number of vertices reached. */
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

/* Unreached pairs from the 2B orbit representatives (L_(i,e), R_(j,e)). */
static long cover_cost(void) {
    int N = GN, V = 2 * curB * N;
    long cost = 0;
    for (int i = 0; i < curB; i++) cost += (long)(V - bfs_count(i * N));
    for (int j = 0; j < curB; j++) cost += (long)(V - bfs_count((curB + j) * N));
    return cost;
}

/* Simulated annealing over the voltages; restarts draw a fresh pattern parameter a.
 * Returns 1 with a cost-0 state (curA and vol hold it), 0 on timeout. */
static int search_group(double until) {
    int N = GN, B = curB;
    const int iters = 8000;
    while (now() < until) {
        int a = (B == 1) ? d : 1 + rndint(d / 2);
        set_pattern(B, a);
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
        if (cost == 0) return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ candidates and phases */

static Cand cand[MAXCAND];
static int nc = 0;

static void build_cands(int lo, int hi) {
    nc = 0;
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 2; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            long N = (long)q * c;
            if (N < lo || N > hi) continue;
            if (nc < MAXCAND) {
                Cand cd = {q, p, k, c, (int)N};
                cand[nc++] = cd;
            }
        }
    }
    for (int i = 1; i < nc; i++) {
        Cand t = cand[i];
        int j = i - 1;
        while (j >= 0 && cand[j].N > t.N) { cand[j + 1] = cand[j]; j--; }
        cand[j + 1] = t;
    }
}

/* Save the current state (pattern and voltages) if it beats the best total. */
static void record(int B, Cand cd) {
    int total = 2 * B * cd.N;
    if (total <= bestTotal) return;
    bestTotal = total;
    bestB = B;
    bestA = curA;
    bestN = cd.N;
    bestQ = cd.q;
    bestP = cd.p;
    bestK = cd.k;
    bestC = cd.c;
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) bestVol[i][t] = vol[i][t];
}

/* Binary search over orders for the largest feasible N, then extend above it. */
static void search_phase(int B, int lo, int hi, double until) {
    build_cands(lo, hi);
    curB = B;
    int bestIdx = -1, bestNp = 0;
    int a = 0, b = nc - 1;
    while (a <= b && now() < until) {
        int mid = (a + b) / 2;
        double rem = until - now();
        double slice = rem * 0.2;
        if (slice < 1.5) slice = 1.5;
        if (slice > rem) slice = rem;
        setup_group(cand[mid].q, cand[mid].p, cand[mid].k, cand[mid].c);
        if (search_group(now() + slice)) {
            record(B, cand[mid]);
            if (cand[mid].N > bestNp) { bestNp = cand[mid].N; bestIdx = mid; }
            a = mid + 1;
        } else {
            b = mid - 1;
        }
    }
    if (bestIdx < 0) return;
    int fails = 0, idx = bestIdx + 1;
    while (idx < nc && now() < until && fails < 2) {
        if (cand[idx].N <= bestNp) { idx++; continue; }
        double rem = until - now();
        double slice = rem * 0.6;
        if (slice > rem) slice = rem;
        setup_group(cand[idx].q, cand[idx].p, cand[idx].k, cand[idx].c);
        if (search_group(now() + slice)) {
            record(B, cand[idx]);
            bestNp = cand[idx].N;
            bestIdx = idx;
            idx++;
            fails = 0;
        } else {
            idx++;
            fails++;
        }
    }
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo2 = atoi(argv[5]), hi2 = atoi(argv[6]);
    int lo1 = atoi(argv[7]), hi1 = atoi(argv[8]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    if (hi2 > MAXN - 1) hi2 = MAXN - 1;
    if (hi1 > MAXN - 1) hi1 = MAXN - 1;
    if (lo2 < 2 * d) lo2 = 2 * d;
    if (lo1 < 2 * d) lo1 = 2 * d;

    double tmid = t0 + (t_end - t0) * 0.6;
    if (lo2 <= hi2) search_phase(2, lo2, hi2, tmid);
    if (bestTotal == 0) {
        if (lo1 <= hi1) search_phase(1, lo1, hi1, t_end);
    } else if (bestB == 2) {
        int nlo = bestN + 1;
        if (nlo < lo2) nlo = lo2;
        if (nlo <= hi2) search_phase(2, nlo, hi2, t_end);
    }

    if (bestTotal == 0) {
        printf("0 0\n");
        return 0;
    }

    /* Rebuild the best graph. */
    setup_group(bestQ, bestP, bestK, bestC);
    set_pattern(bestB, bestA);
    for (int i = 0; i < bestB; i++)
        for (int t = 0; t < d; t++) set_dart(i, t, bestVol[i][t]);

    int N = GN, BN = bestB * N, V = 2 * BN, E = BN * d;
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

    /* Full check from every vertex when cheap; the symmetry argument is the fallback. */
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

NEW_C = r'''
/* Multi-orbit metacyclic voltage lifts, B = 2..4 orbits per side.
 * Group: semidirect product Z_m x|_r Z_k, element a*k+b, product
 * (a,b)(c,e) = (a + r^b c mod m, b+e mod k), with r^k = 1 mod m.
 * Dart (i,t) joins L_(i,g) to R_(sig[i][t], g*vol[i][t]); sig[.][t] is a
 * permutation of the B orbits, so each right orbit gets exactly d darts.
 * Usage: prog d D seed time_limit lo_total hi_total
 * Output: "n m" then m lines "u v", or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 1100
#define MAXB 4
#define MAXD 32
#define MAXV (2 * MAXB * MAXN)
#define ITERS 4000
#define MAXCAND 8192

static int d, D;
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
static int powmod_i(int b, int e, int m) {
    long r = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

/* ------------------------------------------------------------ group */

static int N, GM, GK, GR;
static int GT[MAXN * MAXN];
static int GINV[MAXN];
static int PWR[MAXN];

static void setup_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GR = r;
    N = m * k;
    long p = 1 % m;
    for (int b = 0; b < k; b++) {
        PWR[b] = (int)p;
        p = (p * r) % m;
    }
    for (int x = 0; x < N; x++) {
        int a1 = x / k, b1 = x % k;
        for (int y = 0; y < N; y++) {
            int a2 = y / k, b2 = y % k;
            int a = (int)((a1 + (long)PWR[b1] * a2) % m);
            int b = (b1 + b2) % k;
            GT[x * N + y] = a * k + b;
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (GT[x * N + y] == 0) { GINV[x] = y; break; }
}

static int candM[MAXCAND], candK[MAXCAND], candR[MAXCAND], ncand;

static void add_cand(int m, int k, int r) {
    if (ncand < MAXCAND) {
        candM[ncand] = m;
        candK[ncand] = k;
        candR[ncand] = r;
        ncand++;
    }
}

/* All (m, k, r) with m*k = n and r^k = 1 mod m, gcd(r, m) = 1. */
static void list_groups(int n) {
    ncand = 0;
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        if (m == 1) { add_cand(1, k, 0); continue; }
        for (int r = 1; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod_i(r, k, m) != 1) continue;
            add_cand(m, k, r);
        }
    }
}

/* ------------------------------------------------------------ lift state */

static int B;
static int sig[MAXB][MAXD];
static int vol[MAXB][MAXD];
static int fw[MAXB][MAXD][MAXN];
static int bw[MAXB][MAXD][MAXN];
static int incI[MAXB][MAXD], incT[MAXB][MAXD];
static int stampv[MAXV], que[MAXV];
static int stamp_ = 0;

static void set_dart(int i, int t, int x) {
    vol[i][t] = x;
    int xi = GINV[x];
    for (int g = 0; g < N; g++) {
        fw[i][t][g] = GT[g * N + x];
        bw[i][t][g] = GT[g * N + xi];
    }
}

/* Incoming darts of each right orbit j: exactly d of them. */
static void rebuild_inc(void) {
    int cnt[MAXB];
    for (int j = 0; j < B; j++) cnt[j] = 0;
    for (int t = 0; t < d; t++)
        for (int i = 0; i < B; i++) {
            int j = sig[i][t];
            incI[j][cnt[j]] = i;
            incT[j][cnt[j]] = t;
            cnt[j]++;
        }
}

/* Darts of one left orbit with the same target need distinct voltages. */
static int valid_with(int i, int t, int x) {
    for (int t2 = 0; t2 < d; t2++)
        if (t2 != t && sig[i][t2] == sig[i][t] && vol[i][t2] == x) return 0;
    return 1;
}

static void random_pattern(void) {
    for (int t = 0; t < d; t++) {
        int p[MAXB];
        for (int i = 0; i < B; i++) p[i] = i;
        for (int i = B - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = p[i];
            p[i] = p[j];
            p[j] = tmp;
        }
        for (int i = 0; i < B; i++) sig[i][t] = p[i];
    }
    rebuild_inc();
}

static int random_state(void) {
    random_pattern();
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) vol[i][t] = -1 - t;   /* unassigned sentinels */
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) {
            int x = 0, ok = 0;
            for (int tries = 0; tries < 20000 && !ok; tries++) {
                x = rndint(N);
                ok = valid_with(i, t, x);
            }
            if (!ok) return 0;
            set_dart(i, t, x);
        }
    return 1;
}

/* BFS up to depth D from src; returns the number of vertices reached. */
static int bfs_count(int src) {
    int BN = B * N;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    stampv[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < BN) {
                int i = v / N, g = v % N;
                for (int t = 0; t < d; t++) {
                    int u = BN + sig[i][t] * N + fw[i][t][g];
                    if (stampv[u] != stamp_) { stampv[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - BN, j = w / N, y = w % N;
                for (int k = 0; k < d; k++) {
                    int i = incI[j][k], t = incT[j][k];
                    int u = i * N + bw[i][t][y];
                    if (stampv[u] != stamp_) { stampv[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Unreached vertices from the 2B orbit representatives. Zero iff diameter <= D. */
static long cover_cost(void) {
    int BN = B * N, V = 2 * BN;
    long cost = 0;
    for (int i = 0; i < B; i++) cost += (long)(V - bfs_count(i * N));
    for (int j = 0; j < B; j++) cost += (long)(V - bfs_count(BN + j * N));
    return cost;
}

/* Annealing over voltages and pattern swaps. Returns 1 with a cost-0 state
 * left in sig/vol, or 0 on timeout. */
static int anneal(double until) {
    while (now() < until) {
        if (!random_state()) continue;
        long cost = cover_cost();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < ITERS && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / ITERS);
            if (B >= 2 && rnd01() < 0.15) {
                int t = rndint(d);
                int i1 = rndint(B), i2 = rndint(B - 1);
                if (i2 >= i1) i2++;
                int a = sig[i1][t], b = sig[i2][t];
                sig[i1][t] = b;
                sig[i2][t] = a;
                if (!valid_with(i1, t, vol[i1][t]) || !valid_with(i2, t, vol[i2][t])) {
                    sig[i1][t] = a;
                    sig[i2][t] = b;
                    continue;
                }
                rebuild_inc();
                long c2 = cover_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    sig[i1][t] = a;
                    sig[i2][t] = b;
                    rebuild_inc();
                }
            } else {
                int i = rndint(B), t = rndint(d);
                int x = 0, tries = 0;
                do { x = rndint(N); tries++; } while (!valid_with(i, t, x) && tries < 200);
                if (tries >= 200) continue;
                int old = vol[i][t];
                set_dart(i, t, x);
                long c2 = cover_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    set_dart(i, t, old);
                }
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ best state */

static int bestTotal = 0, bestB, bestM, bestK, bestR;
static int bestSig[MAXB][MAXD], bestVol[MAXB][MAXD];

static void record(void) {
    int total = 2 * B * N;
    if (total <= bestTotal) return;
    bestTotal = total;
    bestB = B;
    bestM = GM;
    bestK = GK;
    bestR = GR;
    memcpy(bestSig, sig, sizeof sig);
    memcpy(bestVol, vol, sizeof vol);
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo = atoi(argv[5]), hi = atoi(argv[6]);
    double t0 = now();
    double t_end = t0 + limit * 0.88 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 3 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    if (lo < 2 * d) lo = 2 * d;
    if (hi > 2 * MAXB * (MAXN - 1)) hi = 2 * MAXB * (MAXN - 1);

    while (now() < t_end - 1.0) {
        if (lo > hi) break;
        int start = 2 + rndint(3);
        int Bc = 0, nlo = 0, nhi = 0;
        for (int s = 0; s < 3 && !Bc; s++) {
            int cb = 2 + (start - 2 + s) % 3;
            int a = (lo + 2 * cb - 1) / (2 * cb);
            int b = hi / (2 * cb);
            if (a < d + 1) a = d + 1;
            if (b > MAXN - 1) b = MAXN - 1;
            if (a <= b) {
                Bc = cb;
                nlo = a;
                nhi = b;
            }
        }
        if (!Bc) break;
        int Nc = nlo + rndint(nhi - nlo + 1);
        list_groups(Nc);
        int pick = rndint(ncand);
        setup_group(candM[pick], candK[pick], candR[pick]);
        B = Bc;
        int total = 2 * B * N;
        double rem = t_end - now();
        double slice = rem * 0.3;
        if (slice < 2.0) slice = 2.0;
        if (slice > rem) slice = rem;
        if (anneal(now() + slice)) {
            record();
            lo = total + 1;
        } else if (total > lo) {
            hi = lo + (total - lo) / 2;
        }
    }

    if (bestTotal == 0) {
        printf("0 0\n");
        return 0;
    }

    /* Rebuild the best graph. */
    setup_group(bestM, bestK, bestR);
    B = bestB;
    memcpy(sig, bestSig, sizeof sig);
    memcpy(vol, bestVol, sizeof vol);
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) set_dart(i, t, vol[i][t]);
    rebuild_inc();

    int BN = B * N, V = 2 * BN, E = BN * d;
    static int adj[MAXV][MAXD];
    for (int v = 0; v < BN; v++) {
        int i = v / N, g = v % N;
        for (int t = 0; t < d; t++) adj[v][t] = BN + sig[i][t] * N + fw[i][t][g];
    }
    for (int j = 0; j < B; j++)
        for (int y = 0; y < N; y++) {
            int w = BN + j * N + y;
            for (int k = 0; k < d; k++) {
                int i = incI[j][k], t = incT[j][k];
                adj[w][k] = i * N + bw[i][t][y];
            }
        }

    /* Simple-graph check: no repeated neighbour. */
    for (int v = 0; v < V; v++)
        for (int k = 0; k < d; k++)
            for (int k2 = 0; k2 < k; k2++)
                if (adj[v][k] == adj[v][k2]) {
                    printf("0 0\n");
                    return 0;
                }

    /* Full check from every vertex when cheap. */
    if (V <= 5000) {
        static int vis2[MAXV], q2[MAXV];
        int st2 = 0;
        for (int s = 0; s < V; s++) {
            st2++;
            int head = 0, tail = 0;
            q2[tail++] = s;
            vis2[s] = st2;
            for (int lvl = 0; lvl < D && head < tail; lvl++) {
                int end = tail;
                while (head < end) {
                    int v = q2[head++];
                    for (int k = 0; k < d; k++) {
                        int u = adj[v][k];
                        if (vis2[u] != st2) { vis2[u] = st2; q2[tail++] = u; }
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

    def elapsed():
        return time.monotonic() - t0

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

    if d >= 3 and D >= 3:
        mb = lib.moore_bound(d, D)

        # Stage 1: the affine two-orbit engine, with a reduced share of the time.
        lo2 = max(2 * d, best[0] // 4 + 1, mb // 16)
        hi2 = mb // 4
        lo1 = max(2 * d, best[0] // 2 + 1, mb // 8)
        hi1 = mb // 2
        budget1 = 0.4 * time_limit - elapsed() - 1.0
        if budget1 > 2.0 and (lo2 <= hi2 or lo1 <= hi1):
            try:
                text = lib.run_c(PARENT_C, [d, D, seed, round(budget1, 2),
                                            lo2, hi2, lo1, hi1],
                                 stdin_graph=None, timeout=budget1 + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the best valid graph so far

        # Stage 2: multi-orbit metacyclic lifts, searching only above the current best.
        budget2 = time_limit - elapsed() - 6.0
        lo_t = best[0] + 1
        hi_t = mb
        if budget2 > 3.0 and lo_t <= hi_t:
            try:
                text = lib.run_c(NEW_C, [d, D, seed, round(budget2, 2), lo_t, hi_t],
                                 stdin_graph=None, timeout=budget2 + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
