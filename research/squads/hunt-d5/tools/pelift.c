/* pelift: route-chart lifts over F_2^4 with a letter per controller EDGE (hunt-d5, for (6,5)).
   Controller C: cubic bipartite, m + m vertices (CTRL.edges: "2m" then "u v" lines, A = 0..m-1).  Each edge e = uv
   carries (M_e in GL(4,2), b_e != 0, t_e): lift edges (u,x) ~ (v, M_e x + t_e + lam b_e), lam in F_2.  Degree 3*2 = 6,
   n = 32m.  cost = same-side ordered lift pairs at distance > 4 (exact, BFS from every lift vertex).  The lift is
   simple as long as C is simple.  Annealing moves: change M_e (a random invertible matrix or one flipped entry kept
   invertible), b_e or t_e of a random edge.
   Usage: pelift CTRL.edges seconds seed [OUT]   OUT gets the letters ("u v M b t" per edge, M as 16 bits row-major,
   vectors as 4-bit ints) and OUT.edges the lift edge list when cost 0.  Env T0 (3), COOL (seconds per halving, 15). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
#define MAXM 64
#define NV (2 * MAXM * 16)
#define W ((NV + 63) / 64)
static int m, ne, eu[3 * MAXM], ev[3 * MAXM], nv, nw;
static uint16_t Mx[3 * MAXM]; static int bb[3 * MAXM], tt[3 * MAXM];
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static inline int apply(uint16_t M, int x) { int y = 0; for (int i = 0; i < 4; i++) { int row = (M >> (4 * i)) & 15; y |= (__builtin_popcount(row & x) & 1) << i; } return y; }
static int invertible(uint16_t M) { for (int x = 1; x < 16; x++) if (apply(M, x) == 0) return 0; return 1; }
static int adj[NV][6], deg[NV];
static uint64_t nb[NV][W];
static void build(void) {
    memset(deg, 0, sizeof(int) * nv);
    for (int e = 0; e < ne; e++) for (int x = 0; x < 16; x++) {
        int y0 = apply(Mx[e], x) ^ tt[e];
        for (int l = 0; l < 2; l++) { int y = y0 ^ (l ? bb[e] : 0); int a = eu[e] * 16 + x, b = ev[e] * 16 + y;
            adj[a][deg[a]++] = b; adj[b][deg[b]++] = a; } }
    for (int v = 0; v < nv; v++) { memset(nb[v], 0, 8 * nw); for (int k = 0; k < deg[v]; k++) nb[v][adj[v][k] >> 6] |= 1ULL << (adj[v][k] & 63); }
}
static long cost(void) {
    build(); long far = 0; uint64_t B2[W], B3[W], B4[W];
    int half = m * 16;
    for (int s = 0; s < nv; s++) {
        memset(B2, 0, 8 * nw);
        for (int k = 0; k < deg[s]; k++) { const uint64_t *r = nb[adj[s][k]]; for (int w = 0; w < nw; w++) B2[w] |= r[w]; }
        memset(B3, 0, 8 * nw);
        for (int w = 0; w < nw; w++) { uint64_t z = B2[w]; while (z) { int y = w * 64 + __builtin_ctzll(z); z &= z - 1; const uint64_t *r = nb[y]; for (int q = 0; q < nw; q++) B3[q] |= r[q]; } }
        memset(B4, 0, 8 * nw);
        for (int w = 0; w < nw; w++) { uint64_t z = B3[w]; while (z) { int y = w * 64 + __builtin_ctzll(z); z &= z - 1; const uint64_t *r = nb[y]; for (int q = 0; q < nw; q++) B4[q] |= r[q]; } }
        int lo = s < half ? 0 : half, cnt = 0;
        for (int t = lo; t < lo + half; t++) if ((B4[t >> 6] >> (t & 63)) & 1) cnt++;
        far += half - cnt;
    }
    return far;
}
static uint16_t randinv(void) { uint16_t M; do M = rnd() & 0xffff; while (!invertible(M)); return M; }
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); int n2; if (fscanf(f, "%d", &n2) != 1) return 2; m = n2 / 2; int a, b; ne = 0;
    while (fscanf(f, "%d %d", &a, &b) == 2) { if (a >= m) { int t = a; a = b; b = t; } eu[ne] = a; ev[ne] = b; ne++; } fclose(f);
    nv = 2 * m * 16; nw = (nv + 63) / 64;
    double secs = atof(argv[2]); rs ^= strtoull(argv[3], 0, 10) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 30; i++) rnd();
    const char *out = argc > 4 ? argv[4] : NULL;
    double T0 = getenv("T0") ? atof(getenv("T0")) : 3, COOL = getenv("COOL") ? atof(getenv("COOL")) : 15;
    for (int e = 0; e < ne; e++) { Mx[e] = randinv(); do bb[e] = rnd() & 15; while (!bb[e]); tt[e] = rnd() & 15; }
    long cur = cost(), best = cur; uint16_t bM[3 * MAXM]; int bB[3 * MAXM], bT[3 * MAXM];
    memcpy(bM, Mx, sizeof Mx); memcpy(bB, bb, sizeof bb); memcpy(bT, tt, sizeof tt);
    double t0 = now(), tl = t0; long it = 0;
    while (best > 0 && now() - t0 < secs) {
        it++; double T = T0 * pow(0.5, (now() - tl) / COOL) + 0.05;
        int e = rnd() % ne; uint16_t oM = Mx[e]; int ob = bb[e], ot = tt[e]; int mv = rnd() % 4;
        if (mv == 0) Mx[e] = randinv();
        else if (mv == 1) { do Mx[e] = oM ^ (1 << (rnd() % 16)); while (!invertible(Mx[e])); }
        else if (mv == 2) { do bb[e] = rnd() & 15; while (!bb[e] || bb[e] == ob); }
        else tt[e] = rnd() & 15;
        long c = cost();
        if (c <= cur || rnd01() < exp(-(double)(c - cur) / (T * 16))) { cur = c;
            if (c < best) { best = c; memcpy(bM, Mx, sizeof Mx); memcpy(bB, bb, sizeof bb); memcpy(bT, tt, sizeof tt);
                fprintf(stderr, "t=%.1f it=%ld best=%ld\n", now() - t0, it, best); } }
        else { Mx[e] = oM; bb[e] = ob; tt[e] = ot; }
        if (now() - tl > 4 * COOL && cur > best) { memcpy(Mx, bM, sizeof Mx); memcpy(bb, bB, sizeof bb); memcpy(tt, bT, sizeof tt); cur = best; tl = now(); }
    }
    memcpy(Mx, bM, sizeof Mx); memcpy(bb, bB, sizeof bb); memcpy(tt, bT, sizeof tt);
    printf("RESULT pelift m=%d n=%d best=%ld iters=%ld time=%.1f\n", m, nv, best, it, now() - t0);
    if (getenv("DIAG")) {   /* far pairs grouped by controller pair (u, u') */
        build(); static int cnt[2 * MAXM][2 * MAXM]; memset(cnt, 0, sizeof cnt); uint64_t B2[W], B3[W], B4[W]; int half = m * 16;
        for (int s0 = 0; s0 < nv; s0++) {
            memset(B2, 0, 8 * nw); for (int k = 0; k < deg[s0]; k++) { const uint64_t *r = nb[adj[s0][k]]; for (int w = 0; w < nw; w++) B2[w] |= r[w]; }
            memset(B3, 0, 8 * nw); for (int w = 0; w < nw; w++) { uint64_t z = B2[w]; while (z) { int y = w * 64 + __builtin_ctzll(z); z &= z - 1; for (int q = 0; q < nw; q++) B3[q] |= nb[y][q]; } }
            memset(B4, 0, 8 * nw); for (int w = 0; w < nw; w++) { uint64_t z = B3[w]; while (z) { int y = w * 64 + __builtin_ctzll(z); z &= z - 1; for (int q = 0; q < nw; q++) B4[q] |= nb[y][q]; } }
            int lo = s0 < half ? 0 : half;
            for (int t = lo; t < lo + half; t++) if (!((B4[t >> 6] >> (t & 63)) & 1)) cnt[s0 / 16][t / 16]++;
        }
        for (int u = 0; u < 2 * m; u++) for (int v = 0; v < 2 * m; v++) if (cnt[u][v]) printf("far ctrl %d -> %d : %d pairs%s\n", u, v, cnt[u][v], u == v ? " (diagonal)" : "");
    }
    if (out && best == 0) {
        FILE *o = fopen(out, "w"); for (int e = 0; e < ne; e++) fprintf(o, "%d %d %u %d %d\n", eu[e], ev[e], Mx[e], bb[e], tt[e]); fclose(o);
        char fn[1024]; snprintf(fn, sizeof fn, "%s.edges", out); o = fopen(fn, "w"); build(); fprintf(o, "%d\n", nv);
        for (int v = 0; v < nv; v++) for (int k = 0; k < deg[v]; k++) if (adj[v][k] > v) fprintf(o, "%d %d\n", v, adj[v][k]);
        fclose(o);
    }
    return best == 0 ? 0 : 1;
}
