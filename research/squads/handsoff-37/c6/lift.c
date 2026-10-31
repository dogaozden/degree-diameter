
/* lift.c: Z_t-symmetric M. Vertices (u,x) = u*t + x, u < k, x in Z_t, m = k*t.
   Base: NE edges (BU,BV,BG) with u < v normalized (M_{(u,x),(v,x+g)} = 1 for all x), and zero loops Z[u]
   (M_{(u,x),(u,x)} = 1 for all x). Each base vertex has 3 stubs. Simulated annealing on the base.
   Usage: lift k t seed seconds T0 T1 iters_per_restart outprefix */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
#define MAXM 128
#define MAXE 200
static int k, t, m;
static uint64_t adj[MAXM][2];
static int NE, BU[MAXE], BV[MAXE], BG[MAXE], Z[MAXM];
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static inline double rndu(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static inline int getadj(int i, int j) { return (adj[i][j >> 6] >> (j & 63)) & 1; }
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

static void rebuild(void) {
    memset(adj, 0, sizeof adj);
    for (int e = 0; e < NE; e++) for (int x = 0; x < t; x++) {
        int a = BU[e] * t + x, b = BV[e] * t + (x + BG[e]) % t;
        adj[a][b >> 6] |= 1ULL << (b & 63); adj[b][a >> 6] |= 1ULL << (a & 63);
    }
    for (int u = 0; u < k; u++) if (Z[u]) for (int x = 0; x < t; x++) { int a = u * t + x; adj[a][a >> 6] |= 1ULL << (a & 63); }
}
/* existence of base edge (u,v,g), normalized */
static int base_exists(int u, int v, int g) {
    if (u > v) { int tt = u; u = v; v = tt; g = (t - g) % t; }
    for (int e = 0; e < NE; e++) if (BU[e] == u && BV[e] == v && BG[e] == g) return 1;
    return 0;
}
static void add_base(int u, int v, int g) {
    if (u > v) { int tt = u; u = v; v = tt; g = (t - g) % t; }
    BU[NE] = u; BV[NE] = v; BG[NE] = g; NE++;
}
static void rem_base(int e) { NE--; BU[e] = BU[NE]; BV[e] = BV[NE]; BG[e] = BG[NE]; }
static int deg_base(int u) { int d = Z[u]; for (int e = 0; e < NE; e++) d += (BU[e] == u) + (BV[e] == u); return d; }

/* ---- cost: unordered pairs {i,j} with no even walk of length <= 6 ---- */
static uint64_t Bw[MAXM][2], H2[MAXM][2];
static int defic[MAXM];
static int cost_full(void) {
    int j, i, w;
    for (j = 0; j < m; j++) {
        uint64_t r0 = 0, r1 = 0;
        for (w = 0; w < 2; w++) {
            uint64_t x = adj[j][w];
            while (x) { int t = __builtin_ctzll(x); x &= x - 1; int k = w * 64 + t; r0 |= adj[k][0]; r1 |= adj[k][1]; }
        }
        Bw[j][0] = r0; Bw[j][1] = r1;
    }
    for (j = 0; j < m; j++) {
        uint64_t r0 = 0, r1 = 0;
        for (w = 0; w < 2; w++) {
            uint64_t x = Bw[j][w];
            while (x) { int t = __builtin_ctzll(x); x &= x - 1; int k = w * 64 + t; r0 |= Bw[k][0]; r1 |= Bw[k][1]; }
        }
        H2[j][0] = r0; H2[j][1] = r1;
    }
    long total = 0;
    for (i = 0; i < m; i++) {
        uint64_t r0 = 0, r1 = 0;
        for (w = 0; w < 2; w++) {
            uint64_t x = Bw[i][w];
            while (x) { int t = __builtin_ctzll(x); x &= x - 1; int k = w * 64 + t; r0 |= H2[k][0]; r1 |= H2[k][1]; }
        }
        int cov = __builtin_popcountll(r0) + __builtin_popcountll(r1);
        defic[i] = m - cov;
        total += m - cov;
    }
    return (int)(total / 2);
}

static void write_cover(const char *fn) {
    FILE *f = fopen(fn, "w");
    if (!f) { perror(fn); return; }
    fprintf(f, "%d\n", 2 * m);
    for (int i = 0; i < m; i++) for (int j = 0; j < m; j++) if (getadj(i, j)) fprintf(f, "%d %d\n", i, m + j);
    fclose(f);
}


static int base_ok(void) { for (int u = 0; u < k; u++) if (deg_base(u) != 3) return 0; return 1; }

/* random base: k vertices, zero loops with parity k mod 2, configuration model over stubs */
static void random_base(void) {
    for (;;) {
        NE = 0; memset(Z, 0, sizeof Z);
        int L = k & 1;
        for (int i = 0; i < L; i++) Z[i] = 1;
        int stubs[3 * MAXM], ns = 0;
        for (int u = 0; u < k; u++) for (int s = 0; s < 3 - Z[u]; s++) stubs[ns++] = u;
        int tries = 0;
        while (ns > 0 && tries < 20000) {
            tries++;
            int p = rndi(ns), q = rndi(ns);
            if (p == q) continue;
            int a = stubs[p], b = stubs[q];
            if (a == b) continue;
            int g = rndi(t);
            if (a == b) continue;
            if (base_exists(a, b, g)) continue;
            add_base(a, b, g);
            int hi = p > q ? p : q, lo = p > q ? q : p;
            stubs[hi] = stubs[ns - 1]; ns--;
            stubs[lo] = stubs[ns - 1]; ns--;
        }
        if (ns == 0) break;
    }
}

static int apply_move(void) {
    double r = rndu();
    if (r < 0.2) { /* voltage change */
        if (NE < 1) return 0;
        int e = rndi(NE), g = rndi(t);
        if (g == BG[e]) return 0;
        for (int f = 0; f < NE; f++) if (f != e && BU[f] == BU[e] && BV[f] == BV[e] && BG[f] == g) return 0;
        BG[e] = g; return 1;
    } else if (r < 0.8) { /* base 2-switch with fresh voltages */
        if (NE < 2) return 0;
        int e1 = rndi(NE), e2 = rndi(NE);
        if (e1 == e2) return 0;
        int a = BU[e1], b = BV[e1], c = BU[e2], d = BV[e2];
        if (rnd() & 1) { int tt2 = c; c = d; d = tt2; }
        if (a == c || b == d) return 0;
        int h1 = rndi(t), h2 = rndi(t);
        /* new edges (a,c,h1), (b,d,h2) */
        if (base_exists(a, c, h1) || base_exists(b, d, h2)) return 0;
        /* remove e1,e2 (higher index first) */
        int hi = e1 > e2 ? e1 : e2, lo = e1 > e2 ? e2 : e1;
        rem_base(hi); rem_base(lo);
        add_base(a, c, h1); add_base(b, d, h2);
        return 1;
    } else if (r < 0.9) { /* zero loop at a slides onto d of edge cd */
        int a = rndi(k); if (!Z[a] || NE < 1) return 0;
        int e = rndi(NE), c = BU[e], d = BV[e];
        if (rnd() & 1) { int tt2 = c; c = d; d = tt2; }
        if (c == a || d == a || Z[d]) return 0;
        int h = rndi(t);
        if (base_exists(a, c, h)) return 0;
        rem_base(e); Z[a] = 0; add_base(a, c, h); Z[d] = 1;
        return 1;
    } else if (r < 0.95) { /* two zero loops -> edge */
        int a = rndi(k), b = rndi(k);
        if (a == b || !Z[a] || !Z[b]) return 0;
        int h = rndi(t);
        if (base_exists(a, b, h)) return 0;
        Z[a] = Z[b] = 0; add_base(a, b, h);
        return 1;
    } else { /* edge -> two zero loops */
        if (NE < 1) return 0;
        int e = rndi(NE), a = BU[e], b = BV[e];
        if (Z[a] || Z[b]) return 0;
        rem_base(e); Z[a] = Z[b] = 1;
        return 1;
    }
}

int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage: lift k t seed seconds T0 T1 iters outprefix\n"); return 2; }
    k = atoi(argv[1]); t = atoi(argv[2]); m = k * t;
    rs ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    double tlim = atof(argv[4]), T0 = atof(argv[5]), T1 = atof(argv[6]);
    long iters = atol(argv[7]);
    const char *outp = argv[8];
    double t0 = now();
    int gbest = 1 << 30;
    char fn[512];
    long total = 0; int restart = 0;
    uint64_t adjc[MAXM][2]; int NEc, BUc[MAXE], BVc[MAXE], BGc[MAXE], Zc[MAXM];
    int sNE = 0, sBU[MAXE], sBV[MAXE], sBG[MAXE], sZ[MAXM];
    int pert = argc > 9 ? atoi(argv[9]) : 0;      /* >0: ILS, restart from best base with pert random moves */
    double Tr0 = argc > 10 ? atof(argv[10]) : T0, Tr1 = argc > 11 ? atof(argv[11]) : T1;
    printf("lift k=%d t=%d m=%d n=%d\n", k, t, m, 2 * m); fflush(stdout);
    while (now() - t0 < tlim) {
        restart++;
        double A0 = T0, A1 = T1;
        if (pert > 0 && sNE > 0 && restart > 1) {
            NE = sNE; memcpy(BU, sBU, sizeof BU); memcpy(BV, sBV, sizeof BV); memcpy(BG, sBG, sizeof BG); memcpy(Z, sZ, sizeof Z);
            for (int p = 0, done = 0; done < pert; p++) { if (apply_move()) done++; }
            A0 = Tr0; A1 = Tr1;
        } else random_base();
        rebuild();
        int cur = cost_full(), rbest = cur;
        double lt0 = log(A0), lt1 = log(A1);
        int rbestNE = -1; int rbBU[MAXE], rbBV[MAXE], rbBG[MAXE], rbZ[MAXM];
        for (long it = 0; it < iters; it++) {
            double T = exp(lt0 + (lt1 - lt0) * (double)it / (double)iters);
            memcpy(adjc, adj, sizeof adj); NEc = NE; memcpy(BUc, BU, sizeof BU); memcpy(BVc, BV, sizeof BV);
            memcpy(BGc, BG, sizeof BG); memcpy(Zc, Z, sizeof Z);
            if (!apply_move()) continue;
            total++;
            rebuild();
            int nc = cost_full();
            int d = nc - cur;
            if (d <= 0 || rndu() < exp(-d / T)) {
                cur = nc;
                if (cur < rbest) { rbest = cur; rbestNE = NE; memcpy(rbBU, BU, sizeof BU); memcpy(rbBV, BV, sizeof BV); memcpy(rbBG, BG, sizeof BG); memcpy(rbZ, Z, sizeof Z); }
                if (cur < gbest) {
                    gbest = cur;
                    snprintf(fn, sizeof fn, "%s_best.edges", outp); write_cover(fn);
                    printf("  new best cost=%d far=%d it=%ld t=%.1f\n", gbest, 2 * gbest, total, now() - t0); fflush(stdout);
                    if (gbest == 0) { printf("ZERO COST m=%d k=%d t=%d\n", m, k, t); goto done; }
                }
            } else {
                memcpy(adj, adjc, sizeof adj); NE = NEc; memcpy(BU, BUc, sizeof BU); memcpy(BV, BVc, sizeof BV);
                memcpy(BG, BGc, sizeof BG); memcpy(Z, Zc, sizeof Z);
            }
        }
        if (rbestNE >= 0 && rbest <= (sNE ? 1 << 30 : 0)) { }
        if (rbestNE >= 0) { sNE = rbestNE; memcpy(sBU, rbBU, sizeof sBU); memcpy(sBV, rbBV, sizeof sBV); memcpy(sBG, rbBG, sizeof sBG); memcpy(sZ, rbZ, sizeof sZ); }
        printf("restart %d rbest=%d cur=%d gbest=%d moves=%ld rate=%.0f/s t=%.0f\n", restart, rbest, cur, gbest, total, total / (now() - t0), now() - t0);
        fflush(stdout);
    }
done:
    printf("FINAL k=%d t=%d m=%d best cost=%d far=%d\n", k, t, m, gbest, 2 * gbest);
    return 0;
}
