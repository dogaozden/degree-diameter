
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


/* ---- tabu over lifts: full neighbourhood of voltage changes + sampled base 2-switches ---- */
static long tabu_v[MAXM][MAXM][64];   /* tabu_v[u][v][g]: re-creating base edge (u,v,g) forbidden until */
typedef struct { int type, p[5]; } cand_t;
static int apply_cand(const cand_t *c) {
    switch (c->type) {
    case 0: { int e = c->p[0], g = c->p[1];
        if (g == BG[e]) return 0;
        for (int f = 0; f < NE; f++) if (f != e && BU[f] == BU[e] && BV[f] == BV[e] && BG[f] == g) return 0;
        BG[e] = g; return 1; }
    case 1: { int e1 = c->p[0], e2 = c->p[1], a = BU[e1], b = BV[e1], cc = BU[e2], d = BV[e2];
        if (e1 == e2) return 0;
        if (c->p[2]) { int tt2 = cc; cc = d; d = tt2; }
        if (a == cc || b == d) return 0;
        if (base_exists(a, cc, c->p[3]) || base_exists(b, d, c->p[4])) return 0;
        int hi = e1 > e2 ? e1 : e2, lo = e1 > e2 ? e2 : e1;
        rem_base(hi); rem_base(lo); add_base(a, cc, c->p[3]); add_base(b, d, c->p[4]); return 1; }
    case 2: { int a = c->p[0], e = c->p[1], cc = BU[e], d = BV[e];
        if (c->p[2]) { int tt2 = cc; cc = d; d = tt2; }
        if (!Z[a] || cc == a || d == a || Z[d] || base_exists(a, cc, c->p[3])) return 0;
        rem_base(e); Z[a] = 0; add_base(a, cc, c->p[3]); Z[d] = 1; return 1; }
    case 3: { int a = c->p[0], b = c->p[1];
        if (a == b || !Z[a] || !Z[b] || base_exists(a, b, c->p[2])) return 0;
        Z[a] = Z[b] = 0; add_base(a, b, c->p[2]); return 1; }
    case 4: { int e = c->p[0], a = BU[e], b = BV[e];
        if (Z[a] || Z[b]) return 0;
        rem_base(e); Z[a] = Z[b] = 1; return 1; }
    }
    return 0;
}
/* the base edges an applied candidate removes (u,v,g normalized) */
static int removed_of(const cand_t *c, int ru[2], int rv[2], int rg[2]) {
    int n = 0;
    if (c->type == 0) { int e = c->p[0]; ru[n] = BU[e]; rv[n] = BV[e]; rg[n] = BG[e]; n++; }
    return n;
}

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: lifttabu k t seed seconds tenure samples outprefix\n"); return 2; }
    k = atoi(argv[1]); t = atoi(argv[2]); m = k * t;
    rs ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    double tlim = atof(argv[4]); long tenure = atol(argv[5]); int samples = atoi(argv[6]);
    const char *outp = argv[7];
    double t0 = now();
    char fn[512];
    random_base(); rebuild();
    int cur = cost_full(), gbest = cur;
    printf("lifttabu k=%d t=%d m=%d init=%d\n", k, t, m, cur); fflush(stdout);
    static uint64_t adjc[MAXM][2]; int NEc, BUc[MAXE], BVc[MAXE], BGc[MAXE], Zc[MAXM];
    long step = 0;
    while (now() - t0 < tlim) {
        step++;
        cand_t bestc; int bestv = 1 << 30, have = 0;
        /* enumerate voltage changes */
        int nd = 0; (void)nd;
        int tot = NE * (t - 1) + samples;
        for (int q = 0; q < tot; q++) {
            cand_t c;
            if (q < NE * (t - 1)) { c.type = 0; c.p[0] = q / (t - 1); int g = q % (t - 1) + 1; c.p[1] = (BG[c.p[0]] + g) % t; }
            else {
                double r = rndu();
                if (r < 0.9 && NE >= 2) { c.type = 1; c.p[0] = rndi(NE); c.p[1] = rndi(NE); c.p[2] = rnd() & 1; c.p[3] = rndi(t); c.p[4] = rndi(t); }
                else if (r < 0.95) { c.type = 2; c.p[0] = rndi(k); c.p[1] = rndi(NE); c.p[2] = rnd() & 1; c.p[3] = rndi(t); }
                else if (r < 0.98) { c.type = 3; c.p[0] = rndi(k); c.p[1] = rndi(k); c.p[2] = rndi(t); }
                else { c.type = 4; c.p[0] = rndi(NE); }
            }
            /* normalised removed/added triples for tabu */
            int tabu = 0;
            memcpy(adjc, adj, sizeof adj); NEc = NE; memcpy(BUc, BU, sizeof BU); memcpy(BVc, BV, sizeof BV);
            memcpy(BGc, BG, sizeof BG); memcpy(Zc, Z, sizeof Z);
            int ru[2], rv[2], rg[2];
            if (c.type == 0) { removed_of(&c, ru, rv, rg); }
            if (!apply_cand(&c)) continue;
            /* tabu: any added base edge that is tabu */
            for (int e = 0; e < NE && !tabu; e++) {
                int isnew = 1;
                for (int f = 0; f < NEc; f++) if (BUc[f] == BU[e] && BVc[f] == BV[e] && BGc[f] == BG[e]) { isnew = 0; break; }
                if (isnew && tabu_v[BU[e]][BV[e]][BG[e]] > step) tabu = 1;
            }
            rebuild();
            int nc = cost_full();
            if (tabu && nc >= gbest) { /* skip */ }
            else if (nc < bestv || (nc == bestv && (rnd() & 1))) {
                bestv = nc; bestc = c; have = 1;
            }
            memcpy(adj, adjc, sizeof adj); NE = NEc; memcpy(BU, BUc, sizeof BU); memcpy(BV, BVc, sizeof BV);
            memcpy(BG, BGc, sizeof BG); memcpy(Z, Zc, sizeof Z);
        }
        if (!have) continue;
        /* apply best; mark removed base edges tabu for re-creation */
        int ru[2], rv[2], rg[2];
        if (bestc.type == 0) { int e = bestc.p[0]; tabu_v[BU[e]][BV[e]][BG[e]] = step + tenure + rndi(3); }
        else { /* record all base edges that disappear */
            int before[MAXE][3], nb = NE;
            for (int e = 0; e < NE; e++) { before[e][0] = BU[e]; before[e][1] = BV[e]; before[e][2] = BG[e]; }
            (void)before; (void)nb; (void)ru; (void)rv; (void)rg;
        }
        int sNE = NE; int sBU[MAXE], sBV[MAXE], sBG[MAXE];
        memcpy(sBU, BU, sizeof BU); memcpy(sBV, BV, sizeof BV); memcpy(sBG, BG, sizeof BG);
        apply_cand(&bestc);
        /* tabu on the edges that were removed (those present before but not after) */
        for (int e = 0; e < sNE; e++) {
            int still = 0;
            for (int f = 0; f < NE; f++) if (BU[f] == sBU[e] && BV[f] == sBV[e] && BG[f] == sBG[e]) { still = 1; break; }
            if (!still) tabu_v[sBU[e]][sBV[e]][sBG[e]] = step + tenure + rndi(3);
        }
        rebuild();
        cur = cost_full();
        if (cur < gbest) {
            gbest = cur;
            snprintf(fn, sizeof fn, "%s_best.edges", outp); write_cover(fn);
            printf("  step %ld new best cost=%d far=%d t=%.1f\n", step, gbest, 2 * gbest, now() - t0); fflush(stdout);
            if (gbest == 0) { printf("ZERO COST m=%d k=%d t=%d\n", m, k, t); break; }
        }
        if (step % 200 == 0) { printf("  step %ld cur=%d gbest=%d t=%.0f\n", step, cur, gbest, now() - t0); fflush(stdout); }
    }
    printf("FINAL k=%d t=%d m=%d best cost=%d far=%d steps=%ld\n", k, t, m, gbest, 2 * gbest, step);
    return 0;
}
