import time

import lib


# Stage 1: the parent's group-lift search (Z_m x| Z_k2 voltage lifts).
C_GROUP = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define MAXD 16
#define MAXK 8
#define GMAX 2000

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (u64)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}
static int gcd_i(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static long long powmod(long long b, int e, long long m) {
    long long r = 1 % m; b %= m;
    while (e > 0) { if (e & 1) r = r * b % m; b = b * b % m; e >>= 1; }
    return r;
}
static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int d_, D_, K_, G_, N_;
static int *MT = NULL, *RS = NULL;
static int *nb = NULL;
static u64 *rch = NULL, *tmpr = NULL;
static int lay[MAXD][MAXK], VS[MAXD][MAXK];
static int BL[MAXD][MAXK], BV[MAXD][MAXK];
static int *bE = NULL;
static int bEc = 0, bestN = 0;

/* Group Z_m x| Z_k2 with (a,b)(c,e) = (a + r^b c, b + e). Element a*k2+b. */
static int build_group(int m, int k2, int r) {
    int G = m * k2;
    if (G > GMAX) return 0;
    G_ = G;
    free(MT); free(RS);
    MT = malloc(sizeof(int) * (size_t)G * G);
    RS = malloc(sizeof(int) * (size_t)G * G);
    int *pwr = malloc(sizeof(int) * (size_t)k2);
    pwr[0] = 1 % m;
    for (int t = 1; t < k2; t++) pwr[t] = (int)((long long)pwr[t - 1] * r % m);
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G; y++) {
            int c = y / k2, e = y % k2;
            int aa = (int)((a + (long long)pwr[b] * c) % m);
            MT[x * G + y] = aa * k2 + (b + e) % k2;
        }
    }
    for (int g = 0; g < G; g++)
        for (int s = 0; s < G; s++)
            RS[s * G + MT[g * G + s]] = g;
    free(pwr);
    return 1;
}

static void alloc_state(int N) {
    free(nb); free(rch); free(tmpr);
    nb = malloc(sizeof(int) * (size_t)d_ * N);
    rch = malloc(sizeof(u64) * (size_t)N);
    tmpr = malloc(sizeof(u64) * (size_t)N);
    N_ = N;
}

/* Dart (l, i, j, s): A_{i,g} ~ B_{j, g*s}. */
static void setdart(int l, int i, int j, int s) {
    int G = G_, k = K_, N = N_;
    int *row = nb + (size_t)l * N;
    for (int g = 0; g < G; g++) {
        row[i * G + g] = (k + j) * G + MT[g * G + s];
        row[(k + j) * G + g] = i * G + RS[s * G + g];
    }
}

static void apply_dart(int l, int i) { setdart(l, i, lay[l][i], VS[l][i]); }

static void snapshot(void) {
    memcpy(BL, lay, sizeof lay);
    memcpy(BV, VS, sizeof VS);
}

static void restore_snapshot(void) {
    int d = d_, k = K_;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) { lay[l][i] = BL[l][i]; VS[l][i] = BV[l][i]; }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) apply_dart(l, i);
}

/* Cost = unreached (representative, vertex) pairs + heavy penalty for duplicate darts. */
static long long evalcost(void) {
    int N = N_, G = G_, k = K_, d = d_;
    for (int v = 0; v < N; v++) rch[v] = 0;
    for (int b = 0; b < 2 * k; b++) rch[(size_t)b * G] = 1ULL << b;
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            u64 x = rch[v];
            for (int l = 0; l < d; l++) x |= rch[nb[l * N + v]];
            tmpr[v] = x;
        }
        u64 *sw = rch; rch = tmpr; tmpr = sw;
    }
    long long cnt = 0;
    for (int v = 0; v < N; v++) cnt += popc(rch[v]);
    long long unreached = (long long)2 * k * N - cnt;
    long long dup = 0;
    for (int i = 0; i < k; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (lay[l][i] == lay[l2][i] && VS[l][i] == VS[l2][i]) dup++;
    return unreached + 1000 * dup;
}

/* Simulated annealing with iterated-local-search kicks from the best state.
   Returns 1 when a valid graph (cost 0) is in the current state. */
static int search(double tend, int iters, int patience, int maxkick) {
    int k = K_, d = d_, G = G_, N = N_;
    u64 full = (1ULL << (2 * k)) - 1;
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < k; i++) { lay[l][i] = perm[i]; VS[l][i] = rndi(G); }
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) apply_dart(l, i);
    long long cost = evalcost();
    double c0 = (double)(cost > 0 ? cost : 1);
    long long bestc = cost;
    snapshot();
    int last = 0, kicks = 0;

    for (int t = 0; t < iters && cost != 0; t++) {
        if ((t & 63) == 0 && now() > tend) break;
        if (t - last > patience) {
            if (kicks >= maxkick) break;
            kicks++;
            restore_snapshot();
            for (int q = 0; q < 3; q++) {
                int l = rndi(d), i = rndi(k);
                VS[l][i] = rndi(G);
                apply_dart(l, i);
            }
            cost = evalcost();
            if (cost < bestc) { bestc = cost; snapshot(); }
            last = t;
            continue;
        }
        double temp = 0.02 * c0 * (1.0 - (double)t / iters);
        if (temp < 0.3) temp = 0.3;

        if (k >= 2 && rndu() < 0.25) {
            /* Layer-swap move: exchange the B-targets of two A-blocks in one layer. */
            int l = rndi(d);
            int i1 = rndi(k), i2 = rndi(k - 1);
            if (i2 >= i1) i2++;
            int t1 = lay[l][i1], t2 = lay[l][i2];
            lay[l][i1] = t2; lay[l][i2] = t1;
            apply_dart(l, i1);
            apply_dart(l, i2);
            long long c2 = evalcost();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                lay[l][i1] = t1; lay[l][i2] = t2;
                apply_dart(l, i1);
                apply_dart(l, i2);
            }
        } else {
            /* Voltage move: defect-targeted with probability 0.4, otherwise uniform. */
            int l = 0, i = 0, picked = 0;
            if (rndu() < 0.4) {
                int start = rndi(N), v = -1;
                for (int q = 0; q < N; q++) {
                    int w = (start + q) % N;
                    if (rch[w] != full) { v = w; break; }
                }
                if (v >= 0) {
                    int b = v / G;
                    l = rndi(d);
                    if (b < k) i = b;
                    else {
                        int jb = b - k;
                        i = -1;
                        for (int ii = 0; ii < k; ii++)
                            if (lay[l][ii] == jb) { i = ii; break; }
                        if (i < 0) i = rndi(k);
                    }
                    picked = 1;
                }
            }
            if (!picked) { l = rndi(d); i = rndi(k); }
            int old = VS[l][i];
            int nw = rndi(G);
            if (nw == old) continue;
            VS[l][i] = nw;
            apply_dart(l, i);
            long long c2 = evalcost();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                VS[l][i] = old;
                apply_dart(l, i);
            }
        }
        if (cost < bestc) { bestc = cost; last = t; snapshot(); }
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int minN = atoi(argv[5]);
    if (minN < 2) minN = 2;
    if (d_ < 3 || D_ < 3 || d_ > MAXD) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double tend = now() + tl;
    static const int Ks[10] = {1, 1, 1, 2, 2, 2, 3, 3, 4, 5};
    static const int K2s[13] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12};
    static int cand[GMAX + 5];

    while (now() < tend) {
        int k = Ks[rndi(10)];
        if (k > MAXK) k = MAXK;
        int Gmin = (minN + 2 * k - 1) / (2 * k);
        if (Gmin < 2) Gmin = 2;
        Gmin += rndi(Gmin / 30 + 3);
        int k2 = K2s[rndi(13)];
        int m = (Gmin + k2 - 1) / k2;
        if (m < 2) m = 2;
        if (m * k2 > GMAX) continue;
        int nc = 0;
        for (int r = 1; r < m; r++)
            if (gcd_i(r, m) == 1 && powmod(r, k2, m) == 1 % m) cand[nc++] = r;
        if (nc == 0) continue;
        int r = cand[rndi(nc)];
        if (!build_group(m, k2, r)) continue;
        K_ = k;
        alloc_state(2 * k * G_);
        int ok = search(tend, 20000, 3000, 6);
        if (ok && N_ > bestN) {
            int kG = K_ * G_;
            int cnt = kG * d_;
            int *ne = malloc(sizeof(int) * 2 * (size_t)cnt);
            int p = 0;
            for (int u = 0; u < kG; u++)
                for (int l = 0; l < d_; l++) {
                    ne[2 * p] = u;
                    ne[2 * p + 1] = nb[(size_t)l * N_ + u];
                    p++;
                }
            free(bE);
            bE = ne;
            bEc = cnt;
            bestN = N_;
            minN = N_ + 1;
        }
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN, bEc);
    for (int p = 0; p < bEc; p++) printf("%d %d\n", bE[2 * p], bE[2 * p + 1]);
    return 0;
}
'''


# Stage 2: a different search. Start from a valid graph, add two vertices (one per
# side) and repair by simulated annealing on bad-pair count + degree-deficit penalty.
# Moves: degree-preserving double-edge swaps, filling deficits by adding edges,
# and shifting a deficit to a neighbour's edge. Every accepted state keeps bipartiteness
# and max degree <= d. Each time bad pairs reach 0 the graph is saved and grown.
C_SA = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define MAXN 2400
#define WMAX ((MAXN + 63) / 64)
#define MAXDEG 16
#define PHASE_LEN 15000
#define LAM 0.3

static int N, d, D, W;
static int side[MAXN + 4];
static int deg[MAXN + 4];
static int adj[MAXN + 4][MAXDEG];
static int sdeg[MAXN + 4];
static int sadj[MAXN + 4][MAXDEG];
static u64 RA[(MAXN + 4) * WMAX], RB[(MAXN + 4) * WMAX];
static int bestU[MAXN * MAXDEG], bestV[MAXN * MAXDEG];
static int bestM = 0, bestN = 0;
static u64 rs = 88172645463325252ULL;

static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (u64)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}
static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    for (int k = 0; k < deg[u]; k++) if (adj[u][k] == v) return 1;
    return 0;
}
static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}
static void del_one(int u, int v) {
    for (int k = 0; k < deg[u]; k++)
        if (adj[u][k] == v) { adj[u][k] = adj[u][--deg[u]]; return; }
}
static void del_edge(int u, int v) { del_one(u, v); del_one(v, u); }

/* Number of unordered pairs at distance > D (or unreachable). */
static long long bad_pairs(void) {
    int n = N, w = W;
    u64 *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(u64) * (size_t)n * (size_t)w);
    for (int v = 0; v < n; v++) cur[(size_t)v * w + (size_t)(v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < D; t++) {
        for (int v = 0; v < n; v++) {
            u64 *o = nxt + (size_t)v * w;
            const u64 *c = cur + (size_t)v * w;
            for (int q = 0; q < w; q++) o[q] = c[q];
            for (int k = 0; k < deg[v]; k++) {
                const u64 *c2 = cur + (size_t)adj[v][k] * w;
                for (int q = 0; q < w; q++) o[q] |= c2[q];
            }
        }
        u64 *s = cur; cur = nxt; nxt = s;
    }
    long long cnt = 0;
    for (int v = 0; v < n; v++) {
        const u64 *c = cur + (size_t)v * w;
        for (int q = 0; q < w; q++) cnt += popc(c[q]);
    }
    long long unreached = (long long)n * n - cnt;
    return unreached / 2;
}

static long long deficit(void) {
    long long s = 0;
    for (int v = 0; v < N; v++) s += d - deg[v];
    return s;
}

static int grow(void) {
    if (N + 2 > MAXN) return 0;
    side[N] = 0; deg[N] = 0;
    side[N + 1] = 1; deg[N + 1] = 0;
    N += 2;
    W = (N + 63) / 64;
    return 1;
}

static void save_best(void) {
    int m = 0;
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++) {
            int u = adj[v][k];
            if (v < u) { bestU[m] = v; bestV[m] = u; m++; }
        }
    bestM = m;
    bestN = N;
}

static void snapshot(void) {
    for (int v = 0; v < N; v++) {
        sdeg[v] = deg[v];
        memcpy(sadj[v], adj[v], sizeof(int) * MAXDEG);
    }
}
static void restore(void) {
    for (int v = 0; v < N; v++) {
        deg[v] = sdeg[v];
        memcpy(adj[v], sadj[v], sizeof(int) * MAXDEG);
    }
}

static int pick_side_deg(int s) {
    for (int t = 0; t < 400; t++) {
        int v = rndi(N);
        if (side[v] == s && deg[v] > 0) return v;
    }
    return -1;
}

/* Proposal: type 0 swap (mv = a1 b1 a2 b2), type 1 shift (mv = p x y), type 2 add (mv = p q).
   Returns -1 when no valid move was generated. */
static int propose(int mv[4]) {
    static int dA[MAXN + 4], dB[MAXN + 4];
    int nA = 0, nB = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] < d) {
            if (side[v] == 0) dA[nA++] = v;
            else dB[nB++] = v;
        }
    }
    double r = rndu();
    if (r < 0.2 && nA > 0 && nB > 0) {
        int p = dA[rndi(nA)], q = dB[rndi(nB)];
        if (has_edge(p, q)) return -1;
        mv[0] = p; mv[1] = q;
        return 2;
    }
    if (r < 0.5 && nA + nB > 0) {
        int idx = rndi(nA + nB);
        int p = idx < nA ? dA[idx] : dB[idx - nA];
        int s = side[p];
        int x = pick_side_deg(s);
        if (x < 0 || x == p) return -1;
        int y = adj[x][rndi(deg[x])];
        if (has_edge(p, y)) return -1;
        mv[0] = p; mv[1] = x; mv[2] = y;
        return 1;
    }
    int a1 = pick_side_deg(0), a2 = pick_side_deg(0);
    if (a1 < 0 || a2 < 0 || a1 == a2) return -1;
    int b1 = adj[a1][rndi(deg[a1])];
    int b2 = adj[a2][rndi(deg[a2])];
    if (b1 == b2 || has_edge(a1, b2) || has_edge(a2, b1)) return -1;
    mv[0] = a1; mv[1] = b1; mv[2] = a2; mv[3] = b2;
    return 0;
}

static void apply_move(int type, const int *mv) {
    if (type == 0) {
        del_edge(mv[0], mv[1]);
        del_edge(mv[2], mv[3]);
        add_edge(mv[0], mv[3]);
        add_edge(mv[2], mv[1]);
    } else if (type == 1) {
        del_edge(mv[1], mv[2]);
        add_edge(mv[0], mv[2]);
    } else {
        add_edge(mv[0], mv[1]);
    }
}

static void undo_move(int type, const int *mv) {
    if (type == 0) {
        del_edge(mv[0], mv[3]);
        del_edge(mv[2], mv[1]);
        add_edge(mv[0], mv[1]);
        add_edge(mv[2], mv[3]);
    } else if (type == 1) {
        del_edge(mv[0], mv[2]);
        add_edge(mv[1], mv[2]);
    } else {
        del_edge(mv[0], mv[1]);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    if (d < 2 || d > MAXDEG || D < 2) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();
    double tend = now() + tl;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { printf("0 0\n"); return 0; }
    if (n < 2 || n > MAXN - 4) { printf("0 0\n"); return 0; }
    N = n;
    W = (N + 63) / 64;
    for (int v = 0; v < N; v++) { deg[v] = 0; side[v] = -1; }
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || u >= N || v < 0 || v >= N || u == v) continue;
        if (deg[u] >= d || deg[v] >= d) continue;
        if (has_edge(u, v)) continue;
        add_edge(u, v);
    }

    static int queue[MAXN + 4];
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        int h = 0, t = 0;
        side[s] = 0;
        queue[t++] = s;
        while (h < t) {
            int x = queue[h++];
            for (int k = 0; k < deg[x]; k++) {
                int y = adj[x][k];
                if (side[y] < 0) { side[y] = 1 - side[x]; queue[t++] = y; }
            }
        }
    }
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (side[adj[v][k]] == side[v]) { printf("0 0\n"); return 0; }

    long long bad = bad_pairs();
    if (bad == 0) {
        save_best();
        if (!grow()) goto done;
        bad = bad_pairs();
    }

    while (now() < tend && N + 2 <= MAXN) {
        double cur = (double)bad + LAM * (double)deficit();
        double pbest = cur;
        snapshot();
        int status = 0; /* 1 = success (grown), -1 = cannot grow */
        for (int it = 0; it < PHASE_LEN; it++) {
            if ((it & 31) == 0 && now() > tend) break;
            double T = 2.0 * (1.0 - (double)it / PHASE_LEN) + 0.05;
            int mv[4];
            int type = propose(mv);
            if (type < 0) continue;
            apply_move(type, mv);
            long long nb = bad_pairs();
            double nc = (double)nb + LAM * (double)deficit();
            if (nc <= cur || rndu() < exp(-(nc - cur) / T)) {
                cur = nc;
                bad = nb;
                if (bad == 0) {
                    save_best();
                    if (!grow()) { status = -1; break; }
                    bad = bad_pairs();
                    status = 1;
                    break;
                }
                if (cur < pbest) { pbest = cur; snapshot(); }
            } else {
                undo_move(type, mv);
            }
        }
        if (status == -1) break;
        if (status == 1) continue;
        if (cur > pbest) {
            restore();
            bad = bad_pairs();
        }
    }

done:
    if (bestN == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bestU[i], bestV[i]);
    return 0;
}
'''


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _parse_or_none(out):
    try:
        n, e = lib.parse_graph_text(out)
    except Exception:
        return None
    return (n, e) if n > 0 else None


def build(d, D, seed, time_limit):
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
            if D == 3 and lib.is_prime_power(d - 1):
                return best  # exact optimum

    if d < 3 or D < 3 or d > 16:
        return best

    # Split the budget: group-lift stage, then annealing repair stage seeded from its output.
    total = max(2.0, time_limit - 5.0)
    g_budget = round(total * 0.45, 2)
    s_budget = round(total - g_budget, 2)

    try:
        out = lib.run_c(C_GROUP, [d, D, seed, g_budget, best_n + 1],
                        timeout=g_budget + 3.0)
        res = _parse_or_none(out)
        if res is not None:
            consider(*res)
    except Exception:
        pass

    try:
        out = lib.run_c(C_SA, [d, D, seed, s_budget], stdin_graph=best,
                        timeout=s_budget + 3.0)
        res = _parse_or_none(out)
        if res is not None:
            consider(*res)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
