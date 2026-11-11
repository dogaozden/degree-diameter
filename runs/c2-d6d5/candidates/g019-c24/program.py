import lib


C_SOURCE = r'''
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
#define GROW 200

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

/* ---------------- shared state ---------------- */
static int d_, D_, K_, G_, N_;
static int *MT = NULL, *RS = NULL;
static int *nb = NULL;
static u64 *rch = NULL, *tmpr = NULL;
static int lay[MAXD][MAXK], VS[MAXD][MAXK];
static int BL[MAXD][MAXK], BV[MAXD][MAXK];
static int *bE = NULL;      /* best valid graph: edge list, A = low labels */
static int bEc = 0, bestN = 0;

/* ---------------- group-lift stage (structured) ---------------- */
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

/* ---------------- repair / growth stage (unstructured) ----------------
   State: bipartite simple graph, max degree d_, sides 0 (A) and 1 (B).
   Moves: add an edge between deficient vertices, or a 2-switch
   (a1b1, a2b2 -> a1b2, a2b1), which keeps all degrees. Cost = ordered
   pairs at distance > D_, via bitsets. When cost hits 0 the graph is
   recorded and a new A-B vertex pair is added, then annealing continues. */
static int RN = 0, RCAP = 0;
static int *rside = NULL, *rdeg = NULL, *rnb = NULL;
static char *radj = NULL;
static u64 *rbA = NULL, *rbB = NULL;
static int *rA = NULL, *rB = NULL;
static int nA = 0, nB = 0;

static void r_add(int a, int b) {
    int d = d_;
    rnb[a * d + rdeg[a]++] = b;
    rnb[b * d + rdeg[b]++] = a;
    radj[a * RCAP + b] = 1;
    radj[b * RCAP + a] = 1;
}

static void r_replace(int v, int old, int nw) {
    int d = d_;
    int *L = rnb + (size_t)v * d;
    for (int i = 0; i < rdeg[v]; i++)
        if (L[i] == old) { L[i] = nw; return; }
}

static void r_del_from(int v, int u) {
    int d = d_;
    int *L = rnb + (size_t)v * d;
    for (int i = 0; i < rdeg[v]; i++)
        if (L[i] == u) { L[i] = L[rdeg[v] - 1]; rdeg[v]--; return; }
}

static void r_del(int a, int b) {
    r_del_from(a, b);
    r_del_from(b, a);
    radj[a * RCAP + b] = 0;
    radj[b * RCAP + a] = 0;
}

/* Requires edges a1-b1, a2-b2 present and a1-b2, a2-b1 absent. Degrees unchanged. */
static void r_switch(int a1, int b1, int a2, int b2) {
    radj[a1 * RCAP + b1] = 0; radj[b1 * RCAP + a1] = 0;
    radj[a2 * RCAP + b2] = 0; radj[b2 * RCAP + a2] = 0;
    radj[a1 * RCAP + b2] = 1; radj[b2 * RCAP + a1] = 1;
    radj[a2 * RCAP + b1] = 1; radj[b1 * RCAP + a2] = 1;
    r_replace(a1, b1, b2);
    r_replace(b1, a1, a2);
    r_replace(a2, b2, b1);
    r_replace(b2, a2, a1);
}

/* Bit-parallel count of ordered vertex pairs at distance > D_. */
static long long rcost(void) {
    int N = RN, d = d_;
    int W = (N + 63) / 64;
    u64 *cur = rbA, *nxt = rbB;
    memset(cur, 0, sizeof(u64) * (size_t)N * W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            u64 *dst = nxt + (size_t)v * W;
            const u64 *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int i = 0; i < rdeg[v]; i++) {
                const u64 *s2 = cur + (size_t)rnb[v * d + i] * W;
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
        }
        u64 *tmp = cur; cur = nxt; nxt = tmp;
    }
    long long cnt = 0;
    for (int v = 0; v < N; v++) {
        const u64 *s = cur + (size_t)v * W;
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(s[w]);
        cnt += N - c;
    }
    return cnt;
}

static void repair_grow(void) {
    int a = RN, b = RN + 1;
    rside[a] = 0; rside[b] = 1;
    rA[nA++] = a;
    rB[nB++] = b;
    RN += 2;
}

static void repair_snapshot(void) {
    int d = d_;
    int cnt = 0;
    for (int v = 0; v < RN; v++) if (rside[v] == 0) cnt += rdeg[v];
    int *ne = malloc(sizeof(int) * 2 * (size_t)(cnt > 0 ? cnt : 1));
    int p = 0;
    for (int v = 0; v < RN; v++)
        if (rside[v] == 0)
            for (int i = 0; i < rdeg[v]; i++) {
                ne[2 * p] = v;
                ne[2 * p + 1] = rnb[(size_t)v * d + i];
                p++;
            }
    free(bE);
    bE = ne;
    bEc = cnt;
    bestN = RN;
}

/* Build repair state from a bipartite graph (n0 vertices, m0 edges). Returns 0 if unusable. */
static int repair_init(int n0, int m0, const int *E) {
    int d = d_;
    if (n0 < 2 || n0 > 100000 || m0 < 0) return 0;
    int *dg = calloc((size_t)n0 + 1, sizeof(int));
    for (int e = 0; e < m0; e++) {
        int u = E[2 * e], v = E[2 * e + 1];
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) { free(dg); return 0; }
        dg[u]++; dg[v]++;
    }
    int *off = malloc(sizeof(int) * ((size_t)n0 + 1));
    off[0] = 0;
    for (int v = 0; v < n0; v++) off[v + 1] = off[v] + dg[v];
    int *cl = malloc(sizeof(int) * (size_t)(2 * m0 + 1));
    int *fp = calloc((size_t)n0 + 1, sizeof(int));
    for (int e = 0; e < m0; e++) {
        int u = E[2 * e], v = E[2 * e + 1];
        cl[off[u] + fp[u]++] = v;
        cl[off[v] + fp[v]++] = u;
    }
    int *col = malloc(sizeof(int) * (size_t)n0);
    int *st = malloc(sizeof(int) * (size_t)n0);
    for (int v = 0; v < n0; v++) col[v] = -1;
    int ok = 1;
    for (int s = 0; s < n0 && ok; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int sp = 0;
        st[sp++] = s;
        while (sp > 0 && ok) {
            int u = st[--sp];
            for (int i = off[u]; i < off[u + 1]; i++) {
                int w = cl[i];
                if (col[w] < 0) { col[w] = 1 - col[u]; st[sp++] = w; }
                else if (col[w] == col[u]) { ok = 0; break; }
            }
        }
    }
    free(dg); free(off); free(cl); free(fp); free(st);
    if (!ok) { free(col); return 0; }

    RCAP = n0 + 2 * GROW;
    RN = n0;
    nA = 0; nB = 0;
    rside = malloc(sizeof(int) * (size_t)RCAP);
    rdeg = calloc((size_t)RCAP, sizeof(int));
    rnb = malloc(sizeof(int) * (size_t)RCAP * d);
    radj = calloc((size_t)RCAP * RCAP, 1);
    rA = malloc(sizeof(int) * (size_t)RCAP);
    rB = malloc(sizeof(int) * (size_t)RCAP);
    int W = (RCAP + 63) / 64;
    rbA = malloc(sizeof(u64) * (size_t)RCAP * W);
    rbB = malloc(sizeof(u64) * (size_t)RCAP * W);
    for (int v = 0; v < n0; v++) {
        rside[v] = col[v];
        if (col[v] == 0) rA[nA++] = v;
        else rB[nB++] = v;
    }
    if (nA == 0 || nB == 0) { free(col); return 0; }
    for (int e = 0; e < m0; e++) {
        int u = E[2 * e], v = E[2 * e + 1];
        int a = (col[u] == 0) ? u : v;
        int b = (a == u) ? v : u;
        if (rdeg[a] < d && rdeg[b] < d && !radj[a * RCAP + b]) r_add(a, b);
    }
    free(col);
    return 1;
}

/* Anneal on edge moves until tend. Records each valid graph and grows it. */
static void repair_run(double tend) {
    int d = d_;
    double tstart = now();
    if (tstart >= tend) return;
    const double T0 = 1.5, T1 = 0.08;
    double T = T0;
    long long cost = rcost();
    long long it = 0;
    for (;;) {
        if ((it & 15) == 0) {
            double tn = now();
            if (tn >= tend) break;
            double frac = (tn - tstart) / (tend - tstart);
            if (frac > 1.0) frac = 1.0;
            T = T0 * pow(T1 / T0, frac);
        }
        it++;
        if (cost == 0) {
            if (RN > bestN) repair_snapshot();
            if (RN + 2 > RCAP) break;
            repair_grow();
            cost = rcost();
            continue;
        }
        if (rndu() < 0.35) {
            /* add-edge move between two deficient vertices */
            int a = -1, b = -1;
            for (int tr = 0; tr < 60 && a < 0; tr++) {
                int x = rA[rndi(nA)], y = rB[rndi(nB)];
                if (rdeg[x] < d && rdeg[y] < d && !radj[x * RCAP + y]) { a = x; b = y; }
            }
            if (a < 0) continue;
            r_add(a, b);
            long long c2 = rcost();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else r_del(a, b);
        } else {
            /* 2-switch move, degree preserving */
            int a1 = rA[rndi(nA)];
            int a2 = rA[rndi(nA)];
            if (rdeg[a1] == 0 || rdeg[a2] == 0) continue;
            int b1 = rnb[(size_t)a1 * d + rndi(rdeg[a1])];
            int b2 = rnb[(size_t)a2 * d + rndi(rdeg[a2])];
            if (a1 == a2 || b1 == b2) continue;
            if (radj[a1 * RCAP + b2] || radj[a2 * RCAP + b1]) continue;
            r_switch(a1, b1, a2, b2);
            long long c2 = rcost();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else r_switch(a1, b2, a2, b1);
        }
    }
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

    /* Optional start graph (valid, from the Python side). */
    int in_n = 0, in_m = 0;
    if (scanf("%d %d", &in_n, &in_m) != 2) { in_n = 0; in_m = 0; }
    if (in_n < 0 || in_m < 0) { in_n = 0; in_m = 0; }
    int *in_e = NULL;
    if (in_n > 0 && in_m > 0) {
        in_e = malloc(sizeof(int) * 2 * (size_t)in_m);
        int ok = 1;
        for (int e = 0; e < in_m; e++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
            in_e[2 * e] = u;
            in_e[2 * e + 1] = v;
        }
        if (!ok) { in_n = 0; in_m = 0; }
    }
    if (in_n > 0 && in_m > 0) {
        bestN = in_n;
        bEc = in_m;
        bE = malloc(sizeof(int) * 2 * (size_t)in_m);
        memcpy(bE, in_e, sizeof(int) * 2 * (size_t)in_m);
        if (minN <= bestN) minN = bestN + 1;
    }
    free(in_e);

    double t0 = now();
    double gend = t0 + 0.35 * tl;   /* structured group-lift stage */
    double tend = t0 + tl;          /* unstructured repair/growth stage */

    static const int Ks[10] = {1, 1, 1, 2, 2, 2, 3, 3, 4, 5};
    static const int K2s[13] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12};
    static int cand[GMAX + 5];

    while (now() < gend) {
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
        int ok = search(gend, 20000, 3000, 6);
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

    /* Repair/growth from the best valid graph found so far. */
    if (bestN >= 2 && bE != NULL) {
        if (repair_init(bestN, bEc, bE)) repair_run(tend);
    }

    if (bestN == 0 || bE == NULL) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN, bEc);
    for (int p = 0; p < bEc; p++) printf("%d %d\n", bE[2 * p], bE[2 * p + 1]);
    return 0;
}
'''


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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

    if d < 3 or D < 3:
        return best

    # Reserve 4 s for compile, startup and Python glue. The C engine stops
    # itself at `budget`; the subprocess timeout is a safety net after that.
    budget = max(0.5, time_limit - 4.0)
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best_n + 1],
                        stdin_graph=best, timeout=budget + 2.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
