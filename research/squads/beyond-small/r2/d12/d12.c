/* d12: feasibility of hubs with 3 affine lines (12 old neighbours) + hub-hub edges.
 * Side A hub h: N(h) = 3 lines of B (12 old B-vertices), plus up to 5 B-hub neighbours k, each k with its own
 * 3 lines of A (N(k), 12 old A-vertices). A-old vertex a is reached by h within 5 iff
 *   d(a, N(h)) <= 3   or   d(a, N(k)) <= 2 for some hub neighbour k.
 * This program measures:
 *  E1: uncovered A-vertices U(T) after 3 greedy-chosen B-lines (vs 4 lines: 0 expected);
 *  E2: pairwise compatibility density of 3-line hubs vs 4-line hubs (condition (2), old neighbours only);
 *  E3: how many of U(T) can be covered by 5 A-side triples (B-hub neighbours) chosen greedily from random pool.
 * usage: d12 EDGES SEED */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#define H 16896
#define W 264
#define NLMAX 25344
static int SAMP = 3000;
static int NE3 = 60;
static int MUL4[4][4] = {{0,0,0,0},{0,1,2,3},{0,2,3,1},{0,3,1,2}};
static int adjA[H][16], adjB[H][16];
static unsigned long long rs = 88172645463325252ULL;
static inline unsigned rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (unsigned)(rs >> 11); }
static inline int popw(const uint64_t *a) { int c = 0; for (int i = 0; i < W; i++) c += __builtin_popcountll(a[i]); return c; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static int scal(int l, int a) { int r = 0; for (int k = 0; k < 4; k++) r |= MUL4[l][(a >> (2 * k)) & 3] << (2 * k); return r; }
static void build(int (*adjT)[16], int (*adjS)[16], uint64_t *ball, uint64_t *d2) {
    for (int t = 0; t < H; t++) {
        uint64_t *bl = ball + (size_t)t * W, *dd = d2 + (size_t)t * W;
        dd[t >> 6] |= 1ULL << (t & 63);
        for (int i = 0; i < 16; i++) { int s = adjT[t][i]; bl[s >> 6] |= 1ULL << (s & 63);
            for (int j = 0; j < 16; j++) { int t2 = adjS[s][j]; dd[t2 >> 6] |= 1ULL << (t2 & 63); } }
        for (int w = 0; w < W; w++) { uint64_t m = dd[w]; while (m) { int b = __builtin_ctzll(m); m &= m - 1; int t2 = w * 64 + b;
            for (int i = 0; i < 16; i++) { int s = adjT[t2][i]; bl[s >> 6] |= 1ULL << (s & 63); } } }
    }
}
/* lines of side T: ball = ball of T-vertices; returns count, fills lines[][4] (local T ids), lball (OR of ball over 4 pts) */
static int gen_lines(uint64_t *ball, int (*lines)[4], uint64_t *lball) {
    int dirs[85], nd = 0;
    for (int c = 1; c < 256; c++) { int lead = -1; for (int k = 0; k < 4; k++) if ((c >> (2 * k)) & 3) { lead = (c >> (2 * k)) & 3; break; } if (lead == 1) dirs[nd++] = c; }
    int nl = 0; uint64_t tmp[W];
    for (int cv = 0; cv < 66; cv++) {
        double sc[85];
        for (int di = 0; di < nd; di++) { long tot = 0;
            for (int s = 0; s < 8; s++) { int y = rnd() & 255; memset(tmp, 0, sizeof tmp);
                for (int l = 0; l < 4; l++) { int t = cv * 256 + (y ^ scal(l, dirs[di])); uint64_t *bl = ball + (size_t)t * W; for (int w = 0; w < W; w++) tmp[w] |= bl[w]; }
                tot += popw(tmp); }
            sc[di] = tot / 8.0; }
        for (int k = 0; k < 6; k++) { int bi = 0; for (int di = 1; di < nd; di++) if (sc[di] > sc[bi]) bi = di; sc[bi] = -1;
            int c = dirs[bi], seen[256] = {0};
            for (int y = 0; y < 256; y++) if (!seen[y]) { for (int l = 0; l < 4; l++) { int z = y ^ scal(l, c); seen[z] = 1; lines[nl][l] = cv * 256 + z; } nl++; } }
    }
    for (int i = 0; i < nl; i++) { uint64_t *o = lball + (size_t)i * W; memset(o, 0, W * 8);
        for (int l = 0; l < 4; l++) { uint64_t *bl = ball + (size_t)lines[i][l] * W; for (int w = 0; w < W; w++) o[w] |= bl[w]; } }
    return nl;
}
static int disjoint_lines(int (*L)[4], int i, int j) { for (int x = 0; x < 4; x++) for (int y = 0; y < 4; y++) if (L[i][x] == L[j][y]) return 0; return 1; }
/* greedy k-line set by coverage gain; returns line ids in ch */
static int greedy_lines(int nl, uint64_t *lball, int (*L)[4], int k, int samples, int *ch, uint64_t *covout) {
    uint64_t cov[W]; memset(cov, 0, sizeof cov); int nch = 0;
    for (int step = 0; step < k; step++) {
        int best = -1; long bg = -1;
        for (int s = 0; s < samples; s++) { int i = rnd() % nl; int ok = 1;
            for (int a = 0; a < nch && ok; a++) if (!disjoint_lines(L, i, ch[a])) ok = 0;
            if (!ok) continue;
            uint64_t *o = lball + (size_t)i * W; long g = 0; for (int w = 0; w < W; w++) g += __builtin_popcountll(o[w] & ~cov[w]);
            if (g > bg) { bg = g; best = i; } }
        if (best < 0) break;
        ch[nch++] = best; uint64_t *o = lball + (size_t)best * W; for (int w = 0; w < W; w++) cov[w] |= o[w];
    }
    if (covout) memcpy(covout, cov, sizeof cov);
    return nch;
}
int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: d12 EDGES SEED\n"); return 2; }
    rs ^= (unsigned long long)atoll(argv[2]) * 0x9E3779B97F4A7C15ULL; if (argc > 3) SAMP = atoi(argv[3]); if (argc > 4) NE3 = atoi(argv[4]);
    FILE *f = fopen(argv[1], "r"); long n, u, v; if (fscanf(f, "%ld", &n) != 1 || n != 2 * H) return 3;
    int da[H] = {0}, db[H] = {0};
    while (fscanf(f, "%ld %ld", &u, &v) == 2) { if (u > v) { long t = u; u = v; v = t; } v -= H; adjA[u][da[u]++] = v; adjB[v][db[v]++] = u; }
    fclose(f);
    for (int i = 0; i < H; i++) if (da[i] != 16 || db[i] != 16) { fprintf(stderr, "not 16-regular\n"); return 3; }
    double t0 = now();
    uint64_t *bA = calloc((size_t)H * W, 8), *dB = calloc((size_t)H * W, 8);   /* T=B: A-ball radius 3, B-ball radius 2 */
    uint64_t *bB = calloc((size_t)H * W, 8), *dA = calloc((size_t)H * W, 8);   /* T=A: B-ball radius 3, A-ball radius 2 */
    build(adjB, adjA, bA, dB); build(adjA, adjB, bB, dA);
    static int LB[NLMAX][4], LA[NLMAX][4];
    uint64_t *lballB = malloc((size_t)NLMAX * W * 8), *lballA = malloc((size_t)NLMAX * W * 8);
    int nlB = gen_lines(bA, LB, lballB);   /* lines of B (for A-hubs) */
    int nlA = gen_lines(bB, LA, lballA);   /* lines of A (for B-hub neighbourhoods) */
    fprintf(stderr, "built %.1fs; lines B %d, A %d\n", now() - t0, nlB, nlA);
    /* E1 */
    int T3 = 1500; int (*tri)[12] = malloc(sizeof(int[12]) * T3); int *uncT = malloc(4 * T3); int ntri = 0;
    int (*triL)[3] = malloc(sizeof(int[3]) * T3);
    int hist[20] = {0}; int minU = H;
    for (int tr = 0; tr < T3; tr++) {
        int ch[3]; uint64_t cov[W]; int k = greedy_lines(nlB, lballB, LB, 3, 2000, ch, cov);
        if (k < 3) continue;
        int U = H - popw(cov);
        int m = 0; for (int a = 0; a < 3; a++) for (int y = 0; y < 4; y++) tri[ntri][m++] = LB[ch[a]][y];
        for (int a = 0; a < 3; a++) triL[ntri][a] = ch[a];
        uncT[ntri] = U; ntri++;
        if (U < minU) minU = U;
        int b = U / 50; if (b > 19) b = 19; hist[b]++;
    }
    fprintf(stderr, "E1 3-line B-sets: %d tries, min uncovered A = %d\n", ntri, minU);
    printf("E1 uncovered-A histogram (bins of 50, last bin >= 950):");
    for (int b = 0; b < 20; b++) printf(" %d", hist[b]);
    printf("\n");
    /* 4-line sanity */
    { int ch[4]; uint64_t cov[W]; int k = greedy_lines(nlB, lballB, LB, 4, 3000, ch, cov); printf("E1 4-line greedy: %d lines, uncovered A = %d\n", k, H - popw(cov)); }
    /* E2 compatibility density: 3-line sets (first 400 with smallest U) vs 4-line sets (400 greedy) */
    {
        int m = ntri < 400 ? ntri : 400; int *ord = malloc(4 * ntri); for (int i = 0; i < ntri; i++) ord[i] = i;
        for (int i = 0; i < ntri; i++) for (int j = i + 1; j < ntri; j++) if (uncT[ord[j]] < uncT[ord[i]]) { int t = ord[i]; ord[i] = ord[j]; ord[j] = t; }
        int (*S3)[12] = malloc(sizeof(int[12]) * m); for (int i = 0; i < m; i++) memcpy(S3[i], tri[ord[i]], 48);
        int (*S4)[16] = malloc(sizeof(int[16]) * 400); int m4 = 0;
        for (int t = 0; t < 400; t++) { int ch[4]; uint64_t cov[W]; int k = greedy_lines(nlB, lballB, LB, 4, 1000, ch, cov); if (k < 4) continue;
            int q = 0; for (int a = 0; a < 4; a++) for (int y = 0; y < 4; y++) S4[m4][q++] = LB[ch[a]][y]; m4++; }
        /* compat(h,h'): N disjoint and R(h) meets N(h'), R = d2 of N */
        uint64_t *R = malloc((size_t)(m > m4 ? m : m4) * W * 8);
        for (int pass = 0; pass < 2; pass++) {
            int cnt = pass == 0 ? m : m4; int sz = pass == 0 ? 12 : 16; int (*S)[16] = pass == 0 ? NULL : S4; (void)S;
            int *ids = malloc(sizeof(int) * cnt * sz); for (int i = 0; i < cnt; i++) for (int q = 0; q < sz; q++) ids[i * sz + q] = pass == 0 ? S3[i][q] : S4[i][q];
            for (int i = 0; i < cnt; i++) { uint64_t *o = R + (size_t)i * W; memset(o, 0, W * 8); for (int q = 0; q < sz; q++) { uint64_t *d = dB + (size_t)ids[i * sz + q] * W; for (int w = 0; w < W; w++) o[w] |= d[w]; } }
            long ok = 0, tot = 0;
            for (int i = 0; i < cnt; i++) for (int j = i + 1; j < cnt; j++) { tot++; int dis = 1, meet = 0;
                for (int q = 0; q < sz && dis; q++) for (int r = 0; r < sz; r++) if (ids[i * sz + q] == ids[j * sz + r]) { dis = 0; break; }
                if (!dis) continue;
                for (int r = 0; r < sz; r++) { int t = ids[j * sz + r]; if ((R[(size_t)i * W + (t >> 6)] >> (t & 63)) & 1) { meet = 1; break; } }
                if (meet) ok++; }
            printf("E2 %s-line sets: %d sets, compat density %.4f\n", pass == 0 ? "3" : "4", cnt, tot ? (double)ok / tot : 0.0);
            free(ids);
        }
        free(R);
        /* E3: cover U(T) by 5 B-hub neighbour sets (A-triples, cover = A-vertices within 2 of their 12 vertices) */
        int nshow = 0; long sumres = 0; int zero = 0;
        for (int i = 0; i < m && i < NE3; i++) {
            int id = ord[i]; uint64_t U[W]; for (int w = 0; w < W; w++) U[w] = ~0ULL;
            uint64_t cov[W]; memset(cov, 0, sizeof cov); for (int a = 0; a < 3; a++) { uint64_t *o = lballB + (size_t)triL[id][a] * W; for (int w = 0; w < W; w++) cov[w] |= o[w]; }
            for (int w = 0; w < W; w++) U[w] = ~cov[w];
            int res0 = popw(U);
            int res = res0;
            for (int slot = 0; slot < 5 && res > 0; slot++) {
                int bestc = -1; long bg = -1; int bl3[3];
                for (int s = 0; s < SAMP; s++) { int ls[3]; int ok = 1;
                    for (int a = 0; a < 3; a++) { ls[a] = rnd() % nlA; for (int b = 0; b < a; b++) if (!disjoint_lines(LA, ls[a], ls[b])) ok = 0; }
                    if (!ok) continue;
                    uint64_t g[W]; memset(g, 0, sizeof g);
                    for (int a = 0; a < 3; a++) { uint64_t *o = lballA + (size_t)ls[a] * W; for (int w = 0; w < W; w++) g[w] |= o[w]; }
                    /* cover set is A-within-2 of the 12 points: use dA per point */
                    memset(g, 0, sizeof g);
                    for (int a = 0; a < 3; a++) for (int y = 0; y < 4; y++) { uint64_t *d = dA + (size_t)LA[ls[a]][y] * W; for (int w = 0; w < W; w++) g[w] |= d[w]; }
                    long gain = 0; for (int w = 0; w < W; w++) gain += __builtin_popcountll(g[w] & U[w]);
                    if (gain > bg) { bg = gain; bestc = s; bl3[0] = ls[0]; bl3[1] = ls[1]; bl3[2] = ls[2]; } }
                if (bestc < 0) break;
                uint64_t g[W]; memset(g, 0, sizeof g);
                for (int a = 0; a < 3; a++) for (int y = 0; y < 4; y++) { uint64_t *d = dA + (size_t)LA[bl3[a]][y] * W; for (int w = 0; w < W; w++) g[w] |= d[w]; }
                for (int w = 0; w < W; w++) U[w] &= ~g[w];
                res = popw(U);
            }
            if (nshow < 8) printf("E3 hub %d: 3-line U=%d -> residual after 5 B-hub balls %d\n", i, res0, res);
            nshow++; sumres += res; if (res == 0) zero++;
        }
        printf("E3 summary over %d 3-line sets: fully covered by 5 hub balls: %d, mean residual %.1f\n", nshow, zero, nshow ? (double)sumres / nshow : 0.0);
    }
    fprintf(stderr, "done %.1fs\n", now() - t0);
    return 0;
}
